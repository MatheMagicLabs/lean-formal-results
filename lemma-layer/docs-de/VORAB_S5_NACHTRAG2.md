# Nachtrag 2 zu VORAB_S5.md (10.10.2026, ~06:30), vor dem Start von S5

S5 hat noch nicht begonnen. Neu hinzu kommt die Quelle PPR (Random Walk mit Neustart auf K1s Graph, je Lücke auf den
Importabschluss beschränkt; gnn/VORAB_W1.md, 7e9b44d7). Ihr Recall ist bereits berechnet (ohne Modell und ohne Lean):
PPR-Top-10 allein 37,4 % (K1 28,2 %); Vereinigung S3 ∪ BM25-10 ∪ K1-10 62,6 % → mit PPR-10 71,5 %.
Kandidaten: wie Nachtrag 1, dazu PPR-Top-10 (ppr_top10.json, eingefroren vor dieser Datei), Quelle 'ppr'; alte
Kandidaten behalten Index und Schreibweise, PPR-Kandidaten werden hinten angefügt. Eine einzige Bewertung durch DeepSeek;
der Wert eines Kandidaten hängt nicht von den anderen ab.
Die Rangfolgen von Nachtrag 1 bleiben unverändert ('alle' = v2+BM25+K1 ohne reine PPR-Kandidaten, 'v2_bm25',
'v2_kozit', 'v2'); S5a–S5c werden genau so ausgewertet. Neu: 'alle_ppr' (v2+BM25+K1+PPR) und 'v2_ppr' (v2+PPR), je Top-5
mit Lean geprüft.
- S5d (neu): pass@5 'alle_ppr' > pass@5 'alle' (einseitiger exakter McNemar, alpha 0,05).
Beschreibend: 'v2_ppr' gegen 'v2'; Anteil der Top-5-Plätze, die reine PPR-Kandidaten belegen.
