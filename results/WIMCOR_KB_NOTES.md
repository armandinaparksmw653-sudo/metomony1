# WiMCor knowledge base: what was measured

Benchmark: WiMCor v1.1 (Mathews and Strube 2020, CC BY-SA 3.0): 206000 Wikipedia sentences, place names used literally or for an institute,
team, event or artifact; the referent is a Wikipedia page. Evaluation sample: 3200 sentences of the test partition (1200 literal, 800 institute,
500 team, 500 artifact, 200 event), 681 (place, surface form) pairs.

1. Reachability by Wikidata relations (391 corpus pairs with resolved titles): a direct relation between the place and the referent exists for
   68% (artifact), 75% (institute), 86% (team), 86% (event) of the pairs; the properties are located-in (P131), headquarters (P159), location (P276).
2. Location-based spaces are too weak: the referent is often named after the place but located elsewhere (University of Warwick is in Coventry,
   Glastonbury Festival in Pilton). The relation that matters is name compatibility; location is supporting evidence.
3. Space = elements of the classes of a sort (with subclasses) found by Wikidata entity search on the surface form, united with the elements located
   at the place whose label contains the surface form. Gold referent inside the space (see wimcor_space_report.txt): institute 95%, team 94%,
   event 100%, artifact 58%. Space size over all sorts: median about 30, 90th percentile 150-200.
4. The place of every sentence is an oracle (page of the literal label, or the place of the harvested pair): place linking is not evaluated.
