#!/usr/bin/env python3
"""Wrap Pandoc-rendered Markdown HTML in the Falsify site layout."""
from html import escape
from pathlib import Path
import re
import sys


source, fragment, destination = map(Path, sys.argv[1:4])
output_root = Path(sys.argv[4]) if len(sys.argv) > 4 else Path(".")
content = fragment.read_text(encoding="utf-8")
# Keep links between Markdown documents usable when GitHub Pages serves HTML.
content = re.sub(r'(href="[^"#?]+)\.md([#?][^"]*)?"', r'\1.html\2"', content)

title = source.stem.replace("_", " ").replace("-", " ").title()
is_home = source.as_posix() == "README.md"
depth = len(source.parent.parts)
root_prefix = "../" * depth

if is_home:
    root_prefix = ""
    slug_counts: dict[str, int] = {}

    def add_anchor(match: re.Match[str]) -> str:
        level, label = match.group(1), match.group(2)
        plain = re.sub(r"<[^>]+>", "", label)
        base = re.sub(r"[^a-z0-9]+", "-", plain.lower()).strip("-") or "section"
        count = slug_counts.get(base, 0)
        slug_counts[base] = count + 1
        anchor = f"{base}-{count}" if count else base
        return f'<h{level} id="{anchor}">{label}</h{level}>'

    content = re.sub(r"<h([23])>(.*?)</h[23]>", add_anchor, content, flags=re.S)
    heading_rows = re.findall(r'<h([23]) id="([^"]+)">(.*?)</h[23]>', content, re.S)
    links = "".join(
        '<a class="{}" href="#{}">{}</a>'.format(
            "subheading" if level == "3" else "",
            anchor,
            re.sub(r"<[^>]+>", "", label),
        )
        for level, anchor, label in heading_rows
    )
    aside = (
        '<aside aria-label="Table of contents"><p class="index-label">'
        f"On this page</p><nav>{links}</nav></aside>"
    )
    destination = output_root / "index.html"
else:
    aside = (
        f'<aside><p class="index-label">Project notes</p><nav>'
        f'<a href="{root_prefix}">README</a>'
        f'<a href="{root_prefix}CHANGELOG.html">Changelog</a>'
        "</nav></aside>"
    )
    destination = output_root / destination

page = f'''<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <meta name="description" content="Falsify is a property-based testing library for Nim, with edge-biased generators, shrinking, and reproducible failures.">
    <title>{escape(title)} · Falsify</title>
    <link rel="stylesheet" href="{root_prefix}site.css">
  </head>
  <body>
    <header class="topbar"><a href="{root_prefix}">Falsify / Nim testing</a><span>Property testing · Shrinking · Reproducible seeds</span><a href="https://github.com/raven6941/falsify">GitHub ↗</a></header>
    <div class="layout" id="top">
      {aside}
      <main class="sheet"><div class="folio"><span>Notes / testing tools</span><span>{escape(source.as_posix())}</span></div><article id="readme">{content}</article><footer class="endnote"><a href="{root_prefix}">Project home</a> · <a href="https://github.com/raven6941/falsify">Source repository</a></footer></main>
    </div>
  </body>
</html>
'''
destination.parent.mkdir(parents=True, exist_ok=True)
destination.write_text(page, encoding="utf-8")
