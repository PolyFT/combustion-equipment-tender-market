#!/usr/bin/env python3
"""Multi-source discovery for public combustion/fire/ablation procurement candidates.

This scanner stores *candidates*, not verified market records. It preserves the
existing ThreadPoolExecutor architecture but upgrades discovery from one RSS
endpoint to multiple adapters:

1. China Government Procurement Network (CCGP) announcement-list pages.
2. DuckDuckGo HTML search.
3. Bing RSS search as a fallback.

The project scope is intentionally narrow: fire/combustion experiments and
material ablation/thermal-protection evaluation. Industrial burners, propulsion
combustion, fire-detection/alarm systems, and unrelated fire-suppression systems
are excluded at discovery time where possible.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import datetime as dt
import hashlib
import html
import json
import re
import threading
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from collections import defaultdict
from html.parser import HTMLParser
from pathlib import Path
from typing import Any

USER_AGENT = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/131.0 Safari/537.36 "
    "CombustionTenderMarketBot/2.0"
)
HEADERS = {
    "User-Agent": USER_AGENT,
    "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.6",
}
BING_RSS = "https://www.bing.com/search?format=rss&q={}"
DDG_HTML = "https://html.duckduckgo.com/html/?q={}"

POSITIVE_WEIGHTS = {
    "燃烧": 1,
    "火灾": 1,
    "热释放": 3,
    "量热": 2,
    "锥形量热": 4,
    "微量热": 4,
    "耐火试验炉": 4,
    "耐火": 2,
    "热失控": 4,
    "外部火烧": 4,
    "火烧": 2,
    "热蔓延": 4,
    "燃爆": 3,
    "烟密度": 3,
    "烟气毒性": 4,
    "烟毒": 3,
    "火焰传播": 3,
    "烧蚀": 5,
    "热防护": 4,
    "耐烧蚀": 5,
    "热流": 2,
    "氧指数": 4,
    "ul94": 4,
    "sbi": 4,
    "房间墙角": 4,
    "家具量热": 4,
    "床垫": 2,
    "电缆燃烧": 4,
    "产烟": 2,
    "货舱火灾": 4,
    "航空防火": 4,
    "防火试验": 3,
    "c/sic": 4,
    "sic/sic": 4,
    "c/c": 3,
    "氧乙炔": 4,
    "氧丙烷": 4,
}

EXCLUDE_TERMS = [
    "燃烧法离子色谱",
    "低氮燃烧器",
    "锅炉燃烧器",
    "工业炉燃烧器",
    "炉窑燃烧器",
    "燃烧效率",
    "燃气轮机燃烧室",
    "航空发动机燃烧室",
    "燃烧室性能",
    "喷雾雾化",
    "推进性能",
    "高焓风洞",
    "高超声速流动",
    "气动热力",
    "感烟探测",
    "感温探测",
    "火焰探测器",
    "图像火灾探测",
    "报警控制器",
    "消防机器人",
    "消防炮",
    "灭火无人机",
    "消防水带",
    "灭火器采购",
    "消防车采购",
    "应急演练",
    "消防演练",
]

PROCUREMENT_TERMS = [
    "招标", "采购", "中标", "成交", "合同", "采购意向",
    "询比", "谈判", "候选", "结果公告", "竞争性磋商",
]

A_DOMAINS = {
    "ccgp.gov.cn",
    "cgyx.ccgp.gov.cn",
    "ccgp-shaanxi.gov.cn",
    "bidding.csg.cn",
    "chnenergybidding.com.cn",
    "buy.cnooc.com.cn",
    "csscbidding.com",
    "srm.catarc.ac.cn",
    "shbid.com",
    "scfri.cn",
    "haust.edu.cn",
    "njust.edu.cn",
    "szu.edu.cn",
    "erzhong-heavy.com",
}
B_DOMAINS = {
    "365trade.com.cn",
    "ec.sinopec.com",
    "fj.ccic.com",
    "tongji.edu.cn",
    "cumt.edu.cn",
    "forestry.gov.cn",
    "caac.gov.cn",
    "instrument.com.cn",
}

AMOUNT_RE = re.compile(r"(?<!\d)(\d{1,9}(?:\.\d{1,4})?)\s*(亿元|万元|万|元)")
STATUS_WORDS = ["中标", "成交", "招标", "采购意向", "询比", "谈判", "合同", "候选"]
TAG_RE = re.compile(r"<[^>]+>")
SPACE_RE = re.compile(r"\s+")
DETAIL_LINK_RE = re.compile(r"/cggg/(?:zygg|dfgg)/[^/]+/\d{6}/t\d+_\d+\.htm", re.I)

HOST_LIMITS: dict[str, threading.Semaphore] = defaultdict(lambda: threading.Semaphore(4))


class AnchorParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.anchors: list[dict[str, str]] = []
        self._href = ""
        self._class = ""
        self._text: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag.lower() != "a":
            return
        d = {k.lower(): (v or "") for k, v in attrs}
        self._href = d.get("href", "")
        self._class = d.get("class", "")
        self._text = []

    def handle_data(self, data: str) -> None:
        if self._href:
            self._text.append(data)

    def handle_endtag(self, tag: str) -> None:
        if tag.lower() != "a" or not self._href:
            return
        text = clean_text(" ".join(self._text))
        self.anchors.append({"href": self._href, "class": self._class, "text": text})
        self._href = ""
        self._class = ""
        self._text = []


def clean_text(value: str | None) -> str:
    value = html.unescape(value or "")
    value = TAG_RE.sub(" ", value)
    return SPACE_RE.sub(" ", value).strip()


def canonical_url(url: str) -> str:
    try:
        p = urllib.parse.urlsplit(url.strip())
        q = urllib.parse.parse_qsl(p.query, keep_blank_values=True)
        q = [
            (k, v)
            for k, v in q
            if not k.lower().startswith("utm_") and k.lower() not in {"spm", "from"}
        ]
        return urllib.parse.urlunsplit(
            (p.scheme.lower(), p.netloc.lower(), p.path.rstrip("/"), urllib.parse.urlencode(q), "")
        )
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
    vals = [m.group(0) for m in AMOUNT_RE.finditer(text)]
    return "；".join(dict.fromkeys(vals[:4]))


def extract_status(text: str) -> str:
    hits = [w for w in STATUS_WORDS if w in text]
    return "/".join(hits[:3])


def relevance_score(title: str, snippet: str, query: str = "") -> int:
    text = f"{title} {snippet}".lower()
    if any(term.lower() in text for term in EXCLUDE_TERMS):
        return -100

    score = 0
    for term, weight in POSITIVE_WEIGHTS.items():
        if term.lower() in text:
            score += weight

    if any(w in text for w in PROCUREMENT_TERMS):
        score += 2

    query_tokens = [
        t for t in re.split(r"\s+", query.lower())
        if len(t) >= 2 and not t.startswith("site:")
    ]
    score += min(2, sum(1 for t in query_tokens if t in text))
    return score


def request_text(url: str, timeout: int = 20, retries: int = 2) -> str:
    host = domain_of(url) or "unknown"
    semaphore = HOST_LIMITS[host]
    last_exc: Exception | None = None
    with semaphore:
        for attempt in range(retries + 1):
            try:
                req = urllib.request.Request(url, headers=HEADERS)
                with urllib.request.urlopen(req, timeout=timeout) as resp:
                    raw = resp.read()
                    charset = resp.headers.get_content_charset() or "utf-8"
                    try:
                        return raw.decode(charset, errors="replace")
                    except LookupError:
                        return raw.decode("utf-8", errors="replace")
            except Exception as exc:
                last_exc = exc
                if attempt < retries:
                    time.sleep(0.8 * (2 ** attempt))
    assert last_exc is not None
    raise last_exc


def unwrap_ddg(url: str) -> str:
    url = html.unescape(url)
    if url.startswith("//"):
        url = "https:" + url
    try:
        p = urllib.parse.urlsplit(url)
        qs = urllib.parse.parse_qs(p.query)
        if "uddg" in qs and qs["uddg"]:
            return canonical_url(urllib.parse.unquote(qs["uddg"][0]))
    except Exception:
        pass
    return canonical_url(url)


def make_row(
    *,
    category: str,
    query: str,
    title: str,
    url: str,
    snippet: str = "",
    pub_date: str = "",
    adapter: str,
    grade: str | None = None,
) -> dict[str, Any] | None:
    title = clean_text(title)
    snippet = clean_text(snippet)
    url = canonical_url(url)
    if not title or not url.startswith(("http://", "https://")):
        return None
    score = relevance_score(title, snippet, query)
    if score < 3:
        return None
    combined = f"{title} {snippet}"
    return {
        "category": category,
        "query": query,
        "title": title,
        "url": url,
        "domain": domain_of(url),
        "source_grade": grade or source_grade(url),
        "adapter": adapter,
        "snippet": snippet[:1000],
        "pub_date": pub_date,
        "amount_text": extract_amount(combined),
        "status_text": extract_status(combined),
        "score": score,
    }


def fetch_bing_rss(category: str, query: str) -> tuple[list[dict], dict]:
    started = time.perf_counter()
    url = BING_RSS.format(urllib.parse.quote(query))
    text = request_text(url)
    root = ET.fromstring(text)
    rows: list[dict] = []
    for item in root.findall(".//item"):
        row = make_row(
            category=category,
            query=query,
            title=item.findtext("title") or "",
            url=item.findtext("link") or "",
            snippet=item.findtext("description") or "",
            pub_date=item.findtext("pubDate") or "",
            adapter="bing_rss",
        )
        if row:
            rows.append(row)
    return rows, {
        "adapter": "bing_rss",
        "query": query,
        "raw_hits": len(root.findall(".//item")),
        "filtered_hits": len(rows),
        "seconds": round(time.perf_counter() - started, 3),
    }


def fetch_ddg_html(category: str, query: str) -> tuple[list[dict], dict]:
    started = time.perf_counter()
    url = DDG_HTML.format(urllib.parse.quote(query))
    text = request_text(url)
    parser = AnchorParser()
    parser.feed(text)
    rows: list[dict] = []
    raw_hits = 0
    for a in parser.anchors:
        if "result__a" not in a.get("class", ""):
            continue
        raw_hits += 1
        link = unwrap_ddg(a["href"])
        row = make_row(
            category=category,
            query=query,
            title=a["text"],
            url=link,
            adapter="duckduckgo_html",
        )
        if row:
            rows.append(row)
    return rows, {
        "adapter": "duckduckgo_html",
        "query": query,
        "raw_hits": raw_hits,
        "filtered_hits": len(rows),
        "seconds": round(time.perf_counter() - started, 3),
    }


def listing_page_url(base_url: str, page_index: int) -> str:
    if page_index <= 0:
        return base_url
    return urllib.parse.urljoin(base_url, f"index_{page_index}.htm")


def fetch_ccgp_listing(source: dict[str, Any], page_index: int) -> tuple[list[dict], dict]:
    started = time.perf_counter()
    page_url = listing_page_url(source["base_url"], page_index)
    text = request_text(page_url)
    parser = AnchorParser()
    parser.feed(text)

    rows: list[dict] = []
    raw_hits = 0
    seen: set[str] = set()
    for a in parser.anchors:
        href = urllib.parse.urljoin(page_url, a["href"])
        if not DETAIL_LINK_RE.search(urllib.parse.urlsplit(href).path):
            continue
        title = a["text"]
        if not title:
            continue
        raw_hits += 1
        u = canonical_url(href)
        if u in seen:
            continue
        seen.add(u)
        row = make_row(
            category="ccgp_listing",
            query=source["name"],
            title=title,
            url=u,
            adapter=source["name"],
            grade=source.get("grade", "A"),
        )
        if row:
            rows.append(row)

    return rows, {
        "adapter": source["name"],
        "query": f"page:{page_index}",
        "raw_hits": raw_hits,
        "filtered_hits": len(rows),
        "seconds": round(time.perf_counter() - started, 3),
    }


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
    slot = int(time.time() // 300)
    start = (slot * max_queries) % len(pairs)
    return [pairs[(start + i) % len(pairs)] for i in range(max_queries)]


def build_tasks(
    query_config: dict[str, list[str]],
    source_config: dict[str, Any],
    max_queries: int,
    full_scan: bool,
) -> list[dict[str, Any]]:
    tasks: list[dict[str, Any]] = []

    selected = choose_queries(query_config, max_queries, full_scan)
    adapters = source_config.get("search_adapters", ["duckduckgo_html", "bing_rss"])
    for category, query in selected:
        for adapter in adapters:
            tasks.append({
                "kind": "search",
                "adapter": adapter,
                "category": category,
                "query": query,
            })

    for source in source_config.get("listing_sources", []):
        pages = int(source.get("pages_per_run", 1))
        for page_index in range(max(1, pages)):
            tasks.append({
                "kind": "listing",
                "source": source,
                "page_index": page_index,
            })
    return tasks


def execute_task(task: dict[str, Any]) -> tuple[list[dict], dict]:
    if task["kind"] == "listing":
        return fetch_ccgp_listing(task["source"], task["page_index"])
    adapter = task["adapter"]
    if adapter == "duckduckgo_html":
        return fetch_ddg_html(task["category"], task["query"])
    if adapter == "bing_rss":
        return fetch_bing_rss(task["category"], task["query"])
    raise ValueError(f"Unknown adapter: {adapter}")


def write_markdown(path: Path, rows: list[dict]) -> None:
    rows_sorted = sorted(
        rows,
        key=lambda r: (r.get("first_seen", ""), r.get("score", 0)),
        reverse=True,
    )
    lines = [
        "# 自动扫描候选库",
        "",
        "> 由 GitHub Actions 多源扫描自动发现。它是**候选库，不等同于已核验主表**；进入市场统计前仍需回溯一手公告并核验金额口径。",
        "",
        f"当前候选：**{len(rows_sorted)}** 条。",
        "",
        "| 首次发现 | 类别 | 来源 | 等级 | 状态/金额线索 | 项目 | 链接 |",
        "|---|---|---|:---:|---|---|---|",
    ]
    for r in rows_sorted[:2000]:
        title = str(r.get("title", "")).replace("|", "\\|")
        url = r.get("url", "")
        status_amount = " / ".join(
            x for x in [r.get("status_text", ""), r.get("amount_text", "")] if x
        ).replace("|", "\\|")
        lines.append(
            f"| {r.get('first_seen','')} | {r.get('category','')} | "
            f"{r.get('adapter','')} | {r.get('source_grade','')} | {status_amount} | "
            f"{title} | [打开]({url}) |"
        )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--queries", default="config/queries.json")
    ap.add_argument("--sources", default="config/sources.json")
    ap.add_argument("--output", default="data/auto_candidates.jsonl")
    ap.add_argument("--markdown", default="data/auto_candidates.md")
    ap.add_argument("--max-queries", type=int, default=12)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--full-scan", action="store_true")
    args = ap.parse_args()

    query_config = json.loads(Path(args.queries).read_text(encoding="utf-8"))
    source_config = json.loads(Path(args.sources).read_text(encoding="utf-8"))
    tasks = build_tasks(query_config, source_config, args.max_queries, args.full_scan)

    existing = load_existing(Path(args.output))
    by_url = {canonical_url(r.get("url", "")): r for r in existing if r.get("url")}
    by_title = {
        re.sub(r"\W+", "", r.get("title", "").lower()): r
        for r in existing if r.get("title")
    }
    now = dt.datetime.now(dt.timezone.utc).astimezone().isoformat(timespec="seconds")

    discovered: list[dict] = []
    errors: list[str] = []
    source_stats: list[dict] = []

    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.workers)) as ex:
        futures = {ex.submit(execute_task, task): task for task in tasks}
        for fut in concurrent.futures.as_completed(futures):
            task = futures[fut]
            try:
                rows, meta = fut.result()
                discovered.extend(rows)
                source_stats.append(meta)
            except Exception as exc:
                label = (
                    task.get("adapter")
                    or task.get("source", {}).get("name")
                    or task.get("kind", "unknown")
                )
                q = task.get("query", f"page:{task.get('page_index','')}")
                errors.append(f"{label}: {q}: {type(exc).__name__}: {exc}")
                source_stats.append({
                    "adapter": label,
                    "query": q,
                    "raw_hits": 0,
                    "filtered_hits": 0,
                    "error": f"{type(exc).__name__}: {exc}",
                })

    new_count = 0
    discovered.sort(
        key=lambda r: (
            {"A": 3, "B": 2, "C": 1}.get(r.get("source_grade", "C"), 0),
            r.get("score", 0),
        ),
        reverse=True,
    )
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
    out_path.write_text(
        "\n".join(json.dumps(r, ensure_ascii=False, sort_keys=True) for r in existing_sorted)
        + ("\n" if existing_sorted else ""),
        encoding="utf-8",
    )
    write_markdown(Path(args.markdown), existing)

    adapter_summary: dict[str, dict[str, Any]] = {}
    grouped: dict[str, list[dict]] = defaultdict(list)
    for stat in source_stats:
        grouped[stat.get("adapter", "unknown")].append(stat)
    for adapter, stats in grouped.items():
        adapter_summary[adapter] = {
            "tasks": len(stats),
            "raw_hits": sum(int(s.get("raw_hits", 0)) for s in stats),
            "filtered_hits": sum(int(s.get("filtered_hits", 0)) for s in stats),
            "errors": sum(1 for s in stats if s.get("error")),
            "avg_seconds": round(
                sum(float(s.get("seconds", 0.0)) for s in stats) / max(1, len(stats)),
                3,
            ),
        }

    status = {
        "scanned_at": now,
        "tasks_scanned": len(tasks),
        "queries_selected": len(choose_queries(query_config, args.max_queries, args.full_scan)),
        "new_candidates": new_count,
        "total_candidates": len(existing),
        "discovered_before_dedupe": len(discovered),
        "adapter_summary": adapter_summary,
        "errors": errors[:50],
    }
    Path("data/scan_status.json").write_text(
        json.dumps(status, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )

    print(
        f"Scanned {len(tasks)} tasks; discovered {len(discovered)} filtered results; "
        f"new={new_count}; total={len(existing)}"
    )
    for adapter, stats in sorted(adapter_summary.items()):
        print(
            f"SOURCE {adapter}: tasks={stats['tasks']} raw={stats['raw_hits']} "
            f"filtered={stats['filtered_hits']} errors={stats['errors']} "
            f"avg={stats['avg_seconds']}s"
        )
    for err in errors[:20]:
        print("WARN", err)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
