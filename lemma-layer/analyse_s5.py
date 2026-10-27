"""Auswertung S5 (VORAB_S5.md + Nachtrag 1). Aufruf: python3 analyse_s5.py <Ordner mit s5_kandidaten.jsonl, s5_wahl.json, s5_ergebnisse.jsonl>
Optional: Q1-Ergebnisse in Q1_FILE (platz_ergebnisse.jsonl) für die bindenden Lücken."""
import os, json, sys, os, collections
from scipy.stats import binomtest
D = sys.argv[1]
S3 = os.environ.get('S3_DIR', 'data_s3')  # folder with s3_kandidaten.jsonl, s3_wahl.json, s3_ergebnisse.jsonl (not included)
K = {k['id']: k for k in map(json.loads, open(f'{D}/s5_kandidaten.jsonl', encoding='utf-8'))}
W = {int(k): v for k, v in json.load(open(f'{D}/s5_wahl.json')).items()}
st = {r['id']: r['status'] for r in map(json.loads, open(f'{D}/s5_ergebnisse.jsonl')) if r['v'] == 'S'}
K3 = {k['id']: k for k in map(json.loads, open(f'{S3}/s3_kandidaten.jsonl', encoding='utf-8'))}
W3 = {int(k): v for k, v in json.load(open(f'{S3}/s3_wahl.json')).items()}
st3 = {r['id']: r['status'] for r in map(json.loads, open(f'{S3}/s3_ergebnisse.jsonl')) if r['v'] == 'S'}
test = sorted(i for i in (json.loads(l)['id'] for l in open(os.environ.get('GAPS_FILE', 'kandidaten.jsonl'))) if i % 2 == 1)
ok5 = lambda i, j: K[i]['kandidaten'][j]['name'] == K[i]['human'] or st.get(i * 1000 + j) == 'ok'
ok3 = lambda i, j: K3[i]['kandidaten'][j]['name'] == K3[i]['human'] or st3.get(i * 1000 + j) == 'ok'
out = []
def p(*a): x = ' '.join(map(str, a)); print(x); out.append(x)
def mc(a, b, lab):
    x = sum(a[i] and not b[i] for i in test); y = sum(b[i] and not a[i] for i in test)
    pv = binomtest(x, x + y, .5, alternative='greater').pvalue if x + y else 1.0
    p(f'  {lab}: {sum(a.values())/len(test):.3f} gegen {sum(b.values())/len(test):.3f}; nur links {x}, nur rechts {y}, '
      f'einseitiger exakter McNemar p = {pv:.2e} -> {"BESTÄTIGT" if pv < 0.05 and x > y else "nicht bestätigt"}')
# fehlende Prüfungen
miss = sorted({(i, j) for i in test if i in W for v in W[i].values() for j in v
               if K[i]['kandidaten'][j]['name'] != K[i]['human'] and (i * 1000 + j) not in st})
p(f'S5: Testlücken mit Auswahl {sum(i in W for i in test)}/{len(test)}; ungeprüfte Top-5-Patches {len(miss)}'
  + (f' (z. B. {miss[:5]})' if miss else ''))
R = {}
for lab in ('alle', 'v2_bm25', 'v2_kozit', 'v2', 'alle_ppr', 'v2_ppr'):
    if not all(lab in W[i] for i in test if i in W): continue
    R[lab] = {i: i in W and any(ok5(i, j) for j in W[i][lab]) for i in test}
    t1 = sum(i in W and bool(W[i][lab]) and ok5(i, W[i][lab][0]) for i in test)
    p(f'  {lab:9s} pass@5 {sum(R[lab].values())/len(test):.3f}   Top-1 {t1/len(test):.3f}')
R['S3'] = {i: i in W3 and any(ok3(i, j) for j in W3[i]['alle']) for i in test}
p(f'  S3 alle   pass@5 {sum(R["S3"].values())/len(test):.3f}   Top-1 {sum(i in W3 and ok3(i, W3[i]["alle"][0]) for i in test)/len(test):.3f}')
p('Hypothesen (einseitig, alpha 0,05):')
mc(R['v2_bm25'], R['S3'], 'S5a v2_bm25 > S3')
mc(R['alle'], R['v2_bm25'], 'S5b alle > v2_bm25')
mc(R['v2_kozit'], R['S3'], 'S5c v2_kozit > S3')
if 'alle_ppr' in R: mc(R['alle_ppr'], R['alle'], 'S5d alle_ppr > alle (Nachtrag 2)')
p('Beschreibend:')
same = sum(i in W and i in W3 and set(W[i]['v2']) == set(W3[i]['alle']) for i in test)
p(f'  Plausibilität: S5-Rangfolge "v2" = S3-Top-5 (als Menge) bei {same}/{len(test)} Lücken; pass@5 S5 v2 {sum(R["v2"].values())/len(test):.3f} '
  f'gegen S3 {sum(R["S3"].values())/len(test):.3f}')
rec = collections.Counter()
for i in test:
    for c in K[i]['kandidaten']:
        if c['name'] == K[i]['human']:
            ss = set(c['src'].split('+')); rec['union'] += 1
            for s in ss: rec[s] += 1
            if ss <= {'bm25', 'kozit'}: rec['nur_neu'] += 1
p('  Recall (Name des Menschen unter den Kandidaten): ' + ', '.join(f'{k} {v/len(test):.3f}' for k, v in rec.most_common()))
V2 = {'lean', 'exact', 'simp', 'modell', 'datei'}
slots = collections.Counter(); tot = 0
for i in test:
    if i not in W: continue
    for j in W[i]['alle']:
        ss = set(K[i]['kandidaten'][j]['src'].split('+')); tot += 1
        slots['nur_bm25' if ss == {'bm25'} else 'nur_kozit' if ss == {'kozit'} else 'bm25+kozit' if ss == {'bm25', 'kozit'} else 'v2'] += 1
p('  Top-5-Plätze in "alle": ' + ', '.join(f'{k} {v/tot:.3f}' for k, v in slots.most_common()))
if 'alle_ppr' in R:
    sl2 = collections.Counter(); t2 = 0
    for i in test:
        if i not in W: continue
        for j in W[i]['alle_ppr']:
            ss = set(K[i]['kandidaten'][j]['src'].split('+')); t2 += 1
            sl2['nur_ppr' if ss == {'ppr'} else 'nur_neu_ohne_ppr' if ss <= {'bm25', 'kozit'} else 'neu_mit_ppr' if ss <= {'bm25', 'kozit', 'ppr'} else 'v2'] += 1
    p('  Top-5-Plätze in "alle_ppr": ' + ', '.join(f'{k} {v/t2:.3f}' for k, v in sl2.most_common()))
    p(f'  v2_ppr gegen v2: {sum(R["v2_ppr"].values())/len(test):.3f} gegen {sum(R["v2"].values())/len(test):.3f}')
gew = collections.Counter()
for i in test:
    if R['alle'][i] and not R['S3'][i] and i in W:
        hit = [j for j in W[i]['alle'] if ok5(i, j)]
        ss = set(K[i]['kandidaten'][hit[0]]['src'].split('+'))
        gew['neu' if not ss & V2 else 'v2'] += 1
p(f'  Gewinne von "alle" gegenüber S3 nach Quelle des ersten Treffers: {dict(gew)}')
Q1 = os.environ.get('Q1_FILE', 'platz_ergebnisse.jsonl')
if os.path.exists(Q1):
    P = collections.defaultdict(dict)
    for r in map(json.loads, open(Q1)):
        if r['v'] != 'O': P[r['id']][r['v']] = r['status']
    nb = [i for i in test if i in P and P[i].get('D') != 'ok' and not any(P[i].get(f'R{k}') == 'ok' for k in range(1, 6))]
    p(f'  bindende Lücken (Q1) n = {len(nb)}: ' + ', '.join(f'{lab} {sum(R[lab][i] for i in nb)/max(1, len(nb)):.3f}' for lab in ('alle', 'v2_bm25', 'v2_kozit', 'v2', 'alle_ppr', 'v2_ppr', 'S3') if lab in R))
open(f'{D}/ergebnis_s5.txt', 'w').write('\n'.join(out) + '\n')
