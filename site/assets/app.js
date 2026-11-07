// Filtering and expanding the lemma lists. Everything else on the site is static HTML.
(function () {
  var q = document.getElementById('q');
  var btn = document.getElementById('expand');
  var shown = document.getElementById('shown');
  if (!q) return;
  var lemmas = Array.prototype.slice.call(document.querySelectorAll('details.lemma'));
  function apply() {
    var terms = q.value.toLowerCase().split(/\s+/).filter(Boolean);
    var n = 0;
    lemmas.forEach(function (d) {
      var hay = d.getAttribute('data-q');
      var ok = terms.every(function (t) { return hay.indexOf(t) >= 0; });
      d.hidden = !ok;
      if (ok) n++;
    });
    document.querySelectorAll('.fn, .grp').forEach(function (s) {
      var any = s.querySelector('details.lemma:not([hidden])');
      var hasLemmas = s.querySelector('details.lemma');
      s.hidden = hasLemmas && !any;
    });
    shown.textContent = n + ' of ' + lemmas.length + ' lemmas';
  }
  q.addEventListener('input', apply);
  var open = false;
  btn.addEventListener('click', function () {
    open = !open;
    lemmas.forEach(function (d) { if (!d.hidden) d.open = open; });
    btn.textContent = open ? 'Collapse all' : 'Expand all';
  });
  if (location.hash.length > 1) {
    var t = document.getElementById(decodeURIComponent(location.hash.slice(1)));
    if (t) t.querySelectorAll('details.lemma').forEach(function (d) { d.open = false; });
  }
  apply();
})();
