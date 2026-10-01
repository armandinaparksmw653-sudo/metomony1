# T4 scouting: bridge to implicit coercive subtyping (Luo)

Status: the first-order fragment is proved (`Metonymy.Implicit`). This note records what the full
statement would need, based on reading Luo-Soloviev-Xue, *Coercive subtyping: theory and implementation*
(Information and Computation 2013). It is an assessment, not a result.

## What the full theorem says

For a type theory T specified in a logical framework (LF) and a coherent set C of subtyping judgments,
the coercive extension T[C] is
* a conservative extension of T (the traditional notion), and
* a definitional extension: every T[C]-derivable judgment has an equivalent T-derivable judgment obtained by
  inserting coercions (this is what makes subtyping an abbreviation).

The proof there goes through three calculi (T[C], an auxiliary star-calculus, and T[C]_0K), algorithms that
transform derivations between them, canonical derivations, and a long series of lemmas (up to Lemma 3.21 and
Theorems 3.7 and 3.9). Coherence is used in several places to make the choices of coercion irrelevant.

## What mechanizing it would require

1. Syntax of LF and UTT (or Martin-Lof type theory) with binders, universes, inductive types: de Bruijn
   representation, weakening, substitution, and their lemmas.
2. Typing and judgmental equality as inductive families, including coercive application and coercive
   definition rules.
3. The transformation algorithms and their correctness, on derivations.
4. Coherence in the form the paper uses (defined in a subsystem, because in the full system the coercive
   definition rule would make all coercions equal).

No mechanized version of this development is known to me; the search was not exhaustive.

## Cost estimate

Several person-months for the full statement; the first-order fragment in `Metonymy.Implicit` is the part that
matters for the present system, because certificates only contain predicate sentences with coerced arguments.

## A feasible intermediate target

The classical coherence theorem for coercions in the simply typed lambda calculus with subtyping translated
to explicit coercions (Breazu-Tannen, Coquand, Gunter, Scedrov, *Inheritance as implicit coercion*, 1991; the
reference should be checked). It covers higher-order terms, avoids dependent types, and its proof is
substantially shorter. Estimated effort: a few weeks. It would upgrade the fragment result to simply typed
terms and is the natural next step if a stronger T4 statement is wanted for the paper.

## Recommendation

Keep the first-order fragment as the formal bridge claim, state its scope precisely, and treat the simply
typed coherence theorem as optional future work rather than a dependency of the main contribution.
