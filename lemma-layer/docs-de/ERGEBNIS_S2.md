# Ergebnis S2: die symbolische Schicht v1 Ende-zu-Ende (09.10.2026)

Vorab festgelegt: schicht/VORAB_S2.md (SHA-256 957ed452…). DeepSeek-Prover-V2-7B, 390 Test-Lücken.
Kandidaten = Leans Vorschläge (`rw?`/`apply?` an der Taktik der Lücke) ∪ erste Bezeichner aus 8 Modell-Stichproben;
das menschliche Lemma wird NICHT hinzugefügt. Rang = Modellwert − 1,398·log(1+Nutzung); Lean prüft die ersten 5.

| | Lean-gültige Füllung |
|---|---|
| freie Erzeugung (Stufe 1 + 2) | 11,8 % |
| Schicht v1, Top-1 | 20,0 % |
| **Schicht v1, pass@5** | **34,6 %** |

**S2a bestätigt:** 89 Lücken nur mit der Schicht gelöst, 0 nur mit freier Erzeugung (McNemar p = 2·10⁻²⁷). Jede Lücke,
die das Modell frei löst, löst auch die Schicht.

- Nach Kontext: rw-Listen 46,5 %, simp/grind-Hinweislisten 42,3 %, Term/Argument 24,1 %.
- Recall des menschlichen Lemmas in den Kandidaten: Lean 23,6 %, Modell 16,4 %, **Vereinigung 34,9 %**. Die beiden
  Quellen ergänzen sich. In 118 Lücken ist das menschliche Lemma unter den Top-5, in 17 weiteren trägt ein anderes Lemma.
- pass@5 (34,6 %) liegt fast am Recall-Deckel (34,9 %): Ranking und Prüfung holen fast alles heraus, was die
  Kandidatenliste hergibt. Der Engpass ist jetzt allein die Kandidatenliste.

## Werkzeug symlayer.py (Demo an drei Löchern)
- Lücke 33 (`lineMap_apply`): richtig auf Platz 1, Lean bestätigt; dazu eine zweite gültige Alternative (`coe_lineMap`).
- Lücke 17 (`measureReal_def`): von Lean vorgeschlagen, auf Platz 5, Lean bestätigt.
- Lücke 1 (Termbeweis): keine Kandidaten, weil die Sonde Termbeweise nicht abdeckte – behoben (Termbeweis wird für die
  Suche durch `by apply?` ersetzt), noch nicht erneut getestet.

## Nächster Hebel
Mehr Recall: zusätzliche Kandidatenquellen (`exact?`, `simp?`-Lemmata, Typ-basierte Suche über den Zielausdruck,
mehr Modell-Stichproben, Lemmata aus derselben Datei), dann dieselbe Rangfolge und Lean-Prüfung.
