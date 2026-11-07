// A small Markdown renderer for results/report.md: headings, paragraphs, lists, tables, `code`, **bold**.
import { esc } from './lean.mjs';

const slug = (s) => s.toLowerCase().replace(/`/g, '').replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '');

export function inline(s) {
  const parts = s.split(/(`[^`]+`)/);
  return parts
    .map((p, i) =>
      i % 2 === 1
        ? `<code>${esc(p.slice(1, -1))}</code>`
        : esc(p).replace(/\*\*([^*]+)\*\*/g, '<strong>$1</strong>'),
    )
    .join('');
}

/** Returns `{title, sections: [{id, title, html}]}`; text before the first `##` is `intro`. */
export function renderReport(md) {
  const lines = md.split('\n');
  let title = '';
  const sections = [];
  let cur = { id: 'intro', title: '', body: [] };
  for (const l of lines) {
    if (l.startsWith('# ')) title = l.slice(2).trim();
    else if (l.startsWith('## ')) {
      sections.push(cur);
      const t = l.slice(3).trim();
      cur = { id: slug(t), title: t, body: [] };
    } else cur.body.push(l);
  }
  sections.push(cur);
  const render = (body) => {
    let html = '';
    let i = 0;
    while (i < body.length) {
      const l = body[i];
      if (l.trim() === '') { i++; continue; }
      if (l.startsWith('|')) {
        const rows = [];
        while (i < body.length && body[i].startsWith('|')) rows.push(body[i++]);
        const cells = (r) => r.replace(/^\||\|$/g, '').split('|').map((c) => c.trim());
        const head = cells(rows[0]);
        const data = rows.slice(2).map(cells);
        html += '<div class="tablewrap"><table><thead><tr>' + head.map((h) => `<th>${inline(h)}</th>`).join('') +
          '</tr></thead><tbody>' + data.map((r) => '<tr>' + r.map((c) => `<td>${inline(c)}</td>`).join('') + '</tr>').join('') +
          '</tbody></table></div>';
      } else if (/^- /.test(l)) {
        const items = [];
        while (i < body.length && /^- /.test(body[i])) items.push(body[i++].slice(2));
        html += '<ul>' + items.map((x) => `<li>${inline(x)}</li>`).join('') + '</ul>';
      } else {
        const para = [];
        while (i < body.length && body[i].trim() !== '' && !body[i].startsWith('|') && !/^- /.test(body[i])) para.push(body[i++]);
        html += `<p>${inline(para.join(' '))}</p>`;
      }
    }
    return html;
  };
  return {
    title,
    sections: sections.map((s) => ({ id: s.id, title: s.title, html: render(s.body) })),
  };
}
