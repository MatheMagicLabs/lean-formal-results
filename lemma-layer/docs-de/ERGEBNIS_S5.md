# Ergebnis S5: Schicht v2 + BM25 + Ko-Zitate + Random Walk, mit Lean geprüft (10.10.2026)

Vorab festgelegt: schicht5/VORAB_S5.md (764dfb71), Nachtrag 1 (48c028fb, Ko-Zitate), Nachtrag 2 (eb946974, PPR).
390 Testlücken, DeepSeek-Prover-V2-7B, Rang = Modellwert − 1,398·log(1+Nutzung), Lean prüft die Top-5 je Rangfolge.
15.589 Kandidaten (S3 7.699, neu: BM25 2.851, Ko-Zitate 3.374, PPR 1.665). Lauf 10.10. 09:43–10:45 (Mac).

| Rangfolge | pass@5 | Top-1 |
|---|---|---|
| S3 / v2 | 39,0 % | 19,7 % |
| v2 + BM25 | 43,8 % | 20,3 % |
| v2 + Ko-Zitate | 47,4 % | 22,1 % |
| v2 + BM25 + Ko-Zitate ('alle') | 49,5 % | 23,1 % |
| v2 + PPR | 51,3 % | 22,6 % |
| **v2 + BM25 + Ko-Zitate + PPR** | **54,1 %** | **24,4 %** |

- S5a v2+BM25 > S3: 28 : 9, p = 1,3·10⁻³ — bestätigt
- S5b alle > v2+BM25: 27 : 5, p = 5,7·10⁻⁵ — bestätigt
- S5c v2+Ko-Zitate > S3: 39 : 6, p = 2,7·10⁻⁷ — bestätigt
- S5d alle+PPR > alle: 20 : 2, p = 6,1·10⁻⁵ — bestätigt
Plausibilität: Rangfolge v2 = S3-Top-5 an 390/390 Lücken. Bindende Lücken (Q1, n = 383): alle+PPR 53,3 %, S3 37,9 %.
Recall des menschlichen Lemmas: Vereinigung 71,5 % (PPR 37,4 %, Ko-Zitate 28,2 %, Lean 23,6 %, BM25 20,3 %, Modell 16,4 %).
Top-5-Plätze in alle+PPR: v2 58,6 %, neue Quellen 41,4 % (davon nur PPR 6,8 %).
