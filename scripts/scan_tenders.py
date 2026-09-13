#!/usr/bin/env python3
"""Discover public combustion/fire/ablation procurement candidates.

The scanner intentionally stores *candidates*, not verified market records.
It uses Bing's public RSS search endpoint, rotates query slices every run,
filters to the project's scope, deduplicates URLs/titles, and writes JSONL
plus a human-readable Markdown index. No API key is required.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import datetime as dt
import hashlib
import html
import json
import os
import re
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

USER_AGENT = (
    "Mozilla/5.0 (compatible; CombustionTenderMarketBot/1.0; "
    "+https://github.com/PolyFT/combustion-equipment-tender-market)"
)
BING_RSS = "https://www.bing.com/search?format=rss&q={}"

# Positive terms are deliberately centered on combustion/fire/ablation itself.
POSITIVE_TERMS = [
    "燃烧", "火灾", "热释放", "量热", "耐火", "热失控", "火烧", "热蔓延",
    "燃爆", "烟密度", "烟气", "火焰传播", "烧蚀", "热防护", "热流", "炭化",
    "氧指数", "ul94", "sbi", "房间墙角", "电缆", "货舱", "防火", "耐烧蚀",
]

# Explicitly outside the user's core technical scope.
EXCLUDE_TERMS = [
    "低氮燃烧器", "锅炉燃烧器", "工业炉燃烧器", "炉窑燃烧器",
    "燃烧效率", "燃气轮机燃烧室", "航空发动机燃烧室", "燃烧室性能",
    "喷雾雾化", "推进性能", "高焓风洞", "高超声速流动", "气动热力",
    "感烟探测", "感温探测", "火焰探测器", "图像火灾探测", "报警控制器",
    "消防机器人", "消防炮", "灭火无人机", "消防水带", "灭火器采购",
    "消防车采购", "应急演练", "消防演练",
]

A_DOMAINS = {
    "ccgp.gov.cn", "cgyx.ccgp.gov.cn", "ccgp-shaanxi.gov.cn",
    "bidding.csg.cn", "chnenergybidding.com.cn", "buy.cnooc.com.cn",
    "csscbidding.com", "srm.catarc.ac.cn", "shbid.com",
    "scfri.cn", "haust.edu.cn", "njust.edu.cn", "szu.edu.cn",
}
B_DOMAINS = {
    "365trade.com.cn", "ec.sinopec.com", "fj.ccic.com", "tongji.edu.cn",
    "cumt.edu.cn", "forestry.gov.cn", "caac.gov.cn",
}

AMOUNT_RE = re.compile(r"(?<!\d)(\d{1,9}(?:\.\d{1,4})?)\s*(亿元|万元|万|元)")
STATUS_WORDS = ["中标", "成交", "招标", "采购意向", "询比", "谈判", "合同", "候选"]
TAG_RE = re.compile(r"<[^>]+>")
SPACE_RE = re.compile(r"\s+")


def clean_text(value: str | None) -> str:
    value = html.unescape(value or "")
    value = TAG_RE.sub(" ", value)
    return SPACE_RE.sub(" ", value).strip()


def canonical_url(url: str) -> str:
    try:
        p = urllib.parse.urlsplit(url.strip())
        q = urllib.parse.parse_qsl(p.query, keep_blank_values=True)
        q = [(k, v) for k, v in q if not k.lower().startswith("utm_") and k.lower() not in {"spm", "from"}]
        return urllib.parse.urlunsplit((p.scheme.lower(), p.netloc.lower(), p.path.rstrip("/"), urllib.parse.urlencode(q), ""))
    except Exception:
        return url.strip()


def domain_of(url: str) -> str:
    try:
        host = urllib.parse.urlsplit(url).netloc.lower().split(":")[0]
        return host[4:] if host.startswith("www.") else host
    except Exception:
        return ""


def source_grade(url: str) -> str:
    domain = domain_of(url)
    if any(domain == d or domain.endswith("." + d) for d in A_DOMAINS):
        return "A"
    if any(domain == d or domain.endswith("." + d) for d in B_DOMAINS):
        return "B"
    return "C"


def extract_amount(text: str) -> str:
    vals = []
    for m in AMOUNT_RE.finditer(text):
        vals.append(m.group(0))
    # Keep a few snippets, not a computed total: one page may contain many package values.
    return "；".join(dict.fromkeys(vals[:4]))


def extract_status(text: str) -> str:
    hits = [w for w in STATUS_WORDS if w in text]
    return "/".join(hits[:3])


def relevance_score(title: str, snippet: str, query: str) -> int:
    text = f"{title} {snippet}".lower()
    if any(term.lower() in text for term in EXCLUDE_TERMS):
        return -100
    score = sum(1 for term in POSITIVE_TERMS if term.lower() in text)
    if any(w in text for w in ["招标", "采购", "中标", "成交", "合同", "意向"]):
        score += 2
    # Query terms provide a weak prior but do not override exclusion rules.
    query_tokens = [t for t in re.split(r"\s+", query.lower()) if len(t) >= 2 and not t.startswith("site:")]
    score += min(2, sum(1 for t in query_tokens if t in text))
    return score


def fetch_rss(category: str, query: str, timeout: int = 20) -> list[dict]:
    url = BING_RSS.format(urllib.parse.quote(query))
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "application/rss+xml,application/xml,text/xml"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        data = resp.read()
    root = ET.fromstring(data)
    out = []
    for item in root.findall(".//item"):
        title = clean_text(item.findtext("title"))
        link = canonical_url(clean_text(item.findtext("link")))
        snippet = clean_text(item.findtext("description"))
        pub_date = clean_text(item.findtext("pubDate"))
        if not title or not link:
            continue
        score = relevance_score(title, snippet, query)
        if score < 3:
            continue
        combined = f"{title} {snippet}"
        out.append({
            "category": category,
            "query": query,
            "title": title,
            "url": link,
            "domain": domain_of(link),
            "source_grade": source_grade(link),
            "snippet": snippet[:800],
            "pub_date": pub_date,
            "amount_text": extract_amount(combined),
            "status_text": extract_status(combined),
            "score": score,
        })
    return out


def load_existing(path: Path) -> list[dict]:
    if not path.exists():
        return []
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError:
            pass
    return rows


def choose_queries(config: dict[str, list[str]], max_queries: int, full_scan: bool) -> list[tuple[str, str]]:
    pairs = [(cat, q) for cat, queries in config.items() for q in queries]
    if full_scan or max_queries <= 0 or max_queries >= len(pairs):
        return pairs
    # Rotate deterministically every 5-minute window so the whole corpus is revisited.
    slot = int(time.time() // 300)
    start = (slot * max_queries) % len(pairs)
    return [pairs[(start + i) % len(pairs)] for i in range(max_queries)]


def write_markdown(path: Path, rows: list[dict]) -> None:
    rows_sorted = sorted(rows, key=lambda r: (r.get("first_seen", ""), r.get("score", 0)), reverse=True)
    lines = [
        "# 自动扫描候选库",
        "",
        "> 本表由 GitHub Actions 自动发现。它是**候选库，不等同于已核验主表**；进入市场统计前仍需回溯一手公告并核验金额口径。",
        "",
        f"当前候选：**{len(rows_sorted)}** 条。",
        "",
        "| 首次发现 | 类别 | 等级 | 状态/金额线索 | 项目 | 来源 |",
        "|---|---|:---:|---|---|---|",
    ]
    for r in rows_sorted[:1000]:
        title = str(r.get("title", "")).replace("|", "\\|")
        url = r.get("url", "")
        status_amount = " / ".join(x for x in [r.get("status_text", ""), r.get("amount_text", "")] if x)
        status_amount = status_amount.replace("|", "\\|")
        lines.append(
            f"| {r.get('first_seen','')} | {r.get('category','')} | {r.get('source_grade','')} | "
            f"{status_amount} | {title} | [打开]({url}) |"
        )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--queries", default="config/queries.json")
    ap.add_argument("--output", default="data/auto_candidates.jsonl")
    ap.add_argument("--markdown", default="data/auto_candidates.md")
    ap.add_argument("--max-queries", type=int, default=12)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--full-scan", action="store_true")
    args = ap.parse_args()

    config = json.loads(Path(args.queries).read_text(encoding="utf-8"))
    selected = choose_queries(config, args.max_queries, args.full_scan)
    existing = load_existing(Path(args.output))
    by_url = {canonical_url(r.get("url", "")): r for r in existing if r.get("url")}
    by_title = {re.sub(r"\W+", "", r.get("title", "").lower()): r for r in existing if r.get("title")}
    now = dt.datetime.now(dt.timezone.utc).astimezone().isoformat(timespec="seconds")

    discovered: list[dict] = []
    errors: list[str] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.workers)) as ex:
        futures = {ex.submit(fetch_rss, cat, query): (cat, query) for cat, query in selected}
        for fut in concurrent.futures.as_completed(futures):
            cat, query = futures[fut]
            try:
                discovered.extend(fut.result())
            except Exception as exc:
                errors.append(f"{cat}: {query}: {type(exc).__name__}: {exc}")

    new_count = 0
    for row in discovered:
        u = canonical_url(row["url"])
        title_key = re.sub(r"\W+", "", row["title"].lower())
        if u in by_url or (title_key and title_key in by_title):
            continue
        row["first_seen"] = now
        row["id"] = hashlib.sha1(f"{row['title']}|{u}".encode("utf-8")).hexdigest()[:12]
        by_url[u] = row
        by_title[title_key] = row
        existing.append(row)
        new_count += 1

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    existing_sorted = sorted(existing, key=lambda r: r.get("first_seen", ""))
    out_path.write_text("\n".join(json.dumps(r, ensure_ascii=False, sort_keys=True) for r in existing_sorted) + ("\n" if existing_sorted else ""), encoding="utf-8")
    write_markdown(Path(args.markdown), existing)

    status_path = Path("data/scan_status.json")
    status_path.write_text(json.dumps({
        "scanned_at": now,
        "queries_scanned": len(selected),
        "new_candidates": new_count,
        "total_candidates": len(existing),
        "errors": errors[:20],
    }, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    print(f"Scanned {len(selected)} queries; discovered {len(discovered)} filtered results; new={new_count}; total={len(existing)}")
    for err in errors[:10]:
        print("WARN", err)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
