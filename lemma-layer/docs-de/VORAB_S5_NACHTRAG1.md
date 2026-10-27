# Nachtrag 1 zu VORAB_S5.md (10.10.2026, ~04:00), vor dem Start von S5

S5 hat noch nicht begonnen. Neu hinzu kommt die Quelle K1 (Ko-Zitate, VORAB_F1_K1.md, 78627c3c), deren Recall bereits
berechnet ist (ohne Modell und ohne Lean): K1-Top-10 allein 28,2 %; S3 ∪ BM25-10 51,3 % → S3 ∪ BM25-10 ∪ K1-10 62,6 %.
Kandidaten: S3 ∪ BM25-Top-10 ∪ K1-Top-10 (k1_top10.json, eingefroren vor dieser Datei), Quelle 'kozit'. Eine einzige
Bewertung durch DeepSeek; der Wert eines Kandidaten hängt nicht von den anderen ab, daher ergeben die Rangfolgen auf
Teilmengen der Quellen genau die Rangfolgen, die getrennte Läufe ergeben hätten.
Rangfolgen und Lean-Prüfung der Top-5: 'alle' (v2+BM25+K1), 'v2_bm25', 'v2_kozit', 'v2'.
- S5a (unverändert): pass@5 'v2_bm25' > pass@5 S3 'alle' (einseitiger exakter McNemar, alpha 0,05).
- S5b (neu): pass@5 'alle' > pass@5 'v2_bm25'.
- S5c (neu): pass@5 'v2_kozit' > pass@5 S3 'alle'.
