#!/usr/bin/env python3
"""Wrap Pandoc-rendered README HTML in the Falsify site layout."""
from html import escape
from pathlib import Path
import re
import sys


source, fragment, destination = map(Path, sys.argv[1:4])
content = fragment.read_text(encoding="utf-8")
# Keep links between Markdown documents usable when GitHub Pages serves HTML.
content = re.sub(r'(href="[^"#?]+)\.md([#?][^"]*)?"', r'\1.html\2"', content)

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
page = f'''<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <meta name="description" content="Falsify is a property-based testing library for Nim, with edge-biased generators, shrinking, and reproducible failures.">
    <title>Falsify · Property-based testing for Nim</title>
    <link rel="stylesheet" href="site.css">
  </head>
  <body>
    <header class="topbar"><a href="">Falsify / Nim testing</a><span>Property testing · Shrinking · Reproducible seeds</span><a href="https://github.com/raven6941/falsify">GitHub ↗</a></header>
    <div class="layout" id="top">
      {aside}
      <main class="sheet"><div class="folio"><span>Notes / testing tools</span><span>{escape(source.as_posix())}</span></div><article id="readme">{content}</article><footer class="endnote"><a href="https://github.com/raven6941/falsify">Falsify source repository</a></footer></main>
    </div>
  </body>
</html>
'''
destination.parent.mkdir(parents=True, exist_ok=True)
destination.write_text(page, encoding="utf-8")
