---
source_pdf: yaacov_pedersen_2010.pdf
ocr_method: cursor-vision-triple-merge
verification_status: draft
---

# Transcription (LLM vision OCR)


<!-- page 1 -->

arXiv:0903.4051v1 [math.LO] 24 Mar 2009

# A PROOF OF COMPLETENESS FOR CONTINUOUS FIRST-ORDER LOGIC

## ITAÏ BEN YAACOV AND ARTHUR PAUL PEDERSEN

**Abstract.** Continuous first-order logic has found interest among model theorists who wish to extend the classical analysis of “algebraic” structures (such as fields, group, and graphs) to various natural classes of complete metric structures (such as probability algebras, Hilbert spaces, and Banach spaces). With research in continuous first-order logic preoccupied with studying the model theory of this framework, we find a natural question calls for attention: Is there an interesting set of axioms yielding a completeness result?

The primary purpose of this article is to show that a certain, interesting set of axioms does indeed yield a completeness result for continuous first-order logic. In particular, we show that in continuous first-order logic a set of formulae is (completely) satisfiable if (and only if) it is consistent. From this result it follows that continuous first-order logic also satisfies an *approximated* form of strong completeness, whereby $\Sigma \models \varphi$ (if and) only if $\Sigma \vdash \varphi \mathbin{\dot{-}} 2^{-n}$ for all $n < \omega$. This approximated form of strong completeness asserts that if $\Sigma \models \varphi$, then proofs from $\Sigma$, being finite, can provide arbitrary better approximations of the truth of $\varphi$.

Additionally, we consider a different kind of question traditionally arising in model theory—that of decidability: When is the set of all consequences of a theory (in a countable, recursive language) recursive? Say that a complete theory $T$ is *decidable* if for every sentence $\varphi$, the value $\varphi_T$ is a recursive real, and moreover, uniformly computable from $\varphi$. If $T$ is incomplete, we say it is *decidable* if for every sentence $\varphi$ the real number $\varphi^{\circ}_T$ is uniformly recursive from $\varphi$, where $\varphi^{\circ}_T$ is the maximal value of $\varphi$ consistent with $T$. As in classical first-order logic, it follows from the completeness theorem of continuous first-order logic that if a complete theory admits a recursive (or even recursively enumerable) axiomatization then it is decidable.

## 1. Introduction

Roughly speaking, model theory studies first-order theories and the corresponding classes of their models (i.e., elementary classes). Properties of the first-order theory of a structure can then give direct insight into the structure itself. Investigation thereof was

---

We wish to thank Jeremy Avigad for valuable comments. We also wish to thank Petr Hájek for offering useful remarks and for pointing us to important references. Finally, we wish to thank an anonymous referee for helpful suggestions.

First author supported by ANR chaire d'excellence junior THEMODMET (ANR-06-CEXC-007) and by Marie Curie research network ModNet.

*Revision 856 of 16 March 2009.*

<!-- page 2 -->

classically restricted to so-called “algebraic” structures, such as fields, groups, and graphs. Additionally, in modern model theory one often studies *stable* theories — theories whose models admit a “well-behaved” notion of independence (which, if it exists, is always unique).

*Continuous first-order logic* was developed in [BU] as an extension of classical first-order logic, permitting one to broaden the aforementioned classical analysis of algebraic structures to various natural classes of complete metric structures. (It should be pointed out that classes of complete metric structures cannot be elementary in the classical sense for several reasons. For example, completeness is an infinitary property and is therefore not expressible in classical first-order logic. See also [BBHU08] for a general survey of continuous logic and its applications for various kinds of metric structures arising in functional analysis and probability theory.) For example, the class (of unit balls) of Hilbert spaces and the class of probability algebras are elementary in this sense. (A probability algebra is the Boolean algebra of events of a probability space modulo the null measure ideal, with the metric $d(A, B) = \mu(A \Delta B)$.) Furthermore, the classical notion of stability can easily be extended to continuous first-order logic. Indeed, somewhat unsurprisingly, the classes of Hilbert spaces and probability algebras are stable, independence being orthogonality and probabilistic independence, respectively.

Historically, two groups of logics precede continuous first-order logic. On the one hand, continuous first-order logic has *structural* precursors. The structural precursors are those logics which make use of machinery similar to that of continuous first-order logic yet were never developed to study complete metric structures. Such structural precursors include Chang and Keisler’s continuous logic [CK66], Łukasiewicz’s many-valued logic [Háj98], and Pavelka’s many-valued logic [Pav79]. Chang and Keisler’s logic is much too general for the study of complete metric structures, while Łukasiewicz logic and Pavelka’s logic were developed for different purposes. Nonetheless, continuous first-order logic is an improved variant of Chang and Keisler’s logic. On the other hand, continuous first-order logic has *purposive* precursors. The purposive precursors are those logics which were developed to study complete metric structures yet do not make use of machinery similar to that of continuous first-order logic. The purposive precursors of continuous first-order logic include Henson’s logic for Banach structures [Hen76] and compact abstract theories (“cats”) [Ben03a, Ben03b, Ben05]. Continuous first-order logic does not suffer from several shortcomings of these logics. Importantly, continuous first-order logic is less technically involved than the previous logics and in many respects much closer to classical first-order logic. Still, continuous first-order logic is expressively equivalent to the logic of metric open Hausdorff cats. Continuous first-order logic also generalizes Henson’s logic for Banach structures, and as such, is expressively equivalent to a natural variant of Henson’s logic.

As an extension of classical first-order logic, continuous first-order logic satisfies suitably phrased forms of the compactness theorem, the Löwenheim–Skolem theorems, the

<!-- page 3 -->

diagram arguments, Craig’s interpolation theorem, Beth’s definability theorem, characterizations of quantifier elimination and model completeness, the existence of saturated and homogeneous models results, the omitting types theorem, fundamental results of stability theory, and nearly all other results of elementary model theory. Moreover, continuous first-order logic affords a tractable framework for ultraproduct constructions (and so hull constructions) in applications of model theory in analysis and geometry. In fact, expressing conditions from analysis and geometry feels quite natural in continuous first-order logic, furnishing model theorists and analysts with a common language.

Thus it is clear that continuous first-order logic is of interest to model theorists. Yet with research focused on the model theory of continuous first-order logic and thus semantic features of this framework, a natural question seems to lurk in the background: Is there an interesting set of axioms yielding a completeness result? The answer depends on how one formulates the notion of completeness. To be sure, there is an interesting set of axioms, and, as we will see, a set of formulae is (completely) satisfiable if (and only if) it is consistent. However, as for continuous propositional logic, only an *approximated* form of strong completeness is obtainable. By this we mean that $\Sigma \models \varphi$ only if $\Sigma \vdash \varphi \mathbin{\dot{-}} 2^{-n}$ for all $n < \omega$, which amounts to the idea if $\Sigma \models \varphi$, then proofs from $\Sigma$, being finite, can provide arbitrarily better approximations of the truth of $\varphi$. (*What this means will become clearer below.*) This should hardly be surprising in light of the fact that continuous first-order logic has been developed for complete metric structures equipped with uniformly continuous functions with respect to which formulae take truth values anywhere in $[0, 1]$.

Of course, a different kind of question traditionally arising in model theory is that of decidability: When is the set of all consequences of a theory (in a countable, recursive language) recursive? Again, such questions can be extended to continuous first-order logic. Say that a complete theory $T$ is *decidable* if for every sentence $\varphi$, the value $\varphi_T$ is a recursive real, and moreover, uniformly computable from $\varphi$. If $T$ is incomplete, we say it is *decidable* if for every sentence $\varphi$ the real number $\varphi^{\circ}_T$ is uniformly recursive from $\varphi$, where $\varphi^{\circ}_T$ is the maximal value of $\varphi$ consistent with $T$. (See Definition 9.7. If $T$ is complete, then $\varphi$ takes the same value in all models of $T$, so $\varphi_T$ coincides with $\varphi^{\circ}_T$ and therefore $\varphi^{\circ}_T$ is the unique value of $\varphi$ consistent with $T$.) As in classical first-order logic, it follows from the completeness theorem that if a complete theory admits a recursive (or even recursively enumerable) axiomatization then it is decidable, whence the connection to the present paper.

Following an introduction to Łukasiewicz propositional logic and continuous propositional logic, we offer a definition of the language of continuous first-order logic and then supply a precise formulation of its semantics. Indeed, this paper can also be seen as an effort to precisely organize and unify the various presentations of continuous first-order logic found in the literature which are often intimated in a rough-and-ready form. Finally, we state and usually prove various results needed to reach the goal of this paper: to state and prove the completeness theorem for continuous first-order logic.

<!-- page 4 -->

To follow our intuitions to this end, the structure of our approach is largely borrowed from the classical approach employed to prove the completeness theorem. In particular, we make use of a Henkin-like construction and a weakened version of the deduction theorem of classical first-order logic. Moreover, various definitions and results found in the classical approach are translated to play analogous roles in our development, while from [BU] we take some basic facts and definitions peculiar to continuous first-order logic. It will become apparent, however, that our approach differs from the classical one in many respects. Furthermore, the completeness theorem we offer is formulated with respect to the semantics employed by the model theorist who studies continuous first-order logic. In particular, our work does not exploit an algebraic semantics. Finally, we should note that results of research on the interplay between logical and deductive entailment for both continuous propositional logic and Łukasiewicz propositional logic play a crucial role in getting our feet off the ground so that we may follow our intuitions in the first place [Ben]. (This work of the first author is partially based on the results of work done by Chang [Cha58, Cha59] and Rose and Rosser [RR58] on Łukasiewicz logic.) With this, we set out to the task at hand.

## 2. ŁUKASIEWICZ LOGIC AND CONTINUOUS LOGIC

**Definition 2.1.** Let $\mathcal{S}_0 = \{P_i : i \in I\}$ be a set of distinct symbols. Let $\mathcal{S}$ be freely generated from $\mathcal{S}_0$ by the formal binary operation $\dot{-}$ and the unary operation $\neg$. We call $\mathcal{S}$ a *Łukasiewicz propositional logic*.

**Definition 2.2.** Let $\mathcal{S}$ be a Łukasiewicz propositional logic.

(i) If $v_0 : \mathcal{S}_0 \to [0, 1]$ is a mapping, we can extend $v_0$ to a unique mapping $v : \mathcal{S} \to [0, 1]$ by setting

- $v(\varphi \dot{-} \psi) := \max(v(\varphi) - v(\psi), 0)$.
- $v(\neg \varphi) := 1 - v(\varphi)$.

We call $v$ the *truth assignment* defined by $v_0$.

(ii) If $\Sigma \subseteq \mathcal{S}$, we write $v \vDash \Sigma$ if $v(\varphi) = 0$ for all $\varphi \in \Sigma$, and we call $v$ a *model* of $\Sigma$. We also write $v \vDash \varphi$ if $v \vDash \{\varphi\}$.

(iii) We say that $\Sigma \subseteq \mathcal{S}$ is *satisfiable* if it has a model.

(iv) We write $\Sigma \vDash \varphi$ if every model of $\Sigma$ is a model of $\varphi$.

We may write $\Sigma \vDash^{\mathrm{L}} \varphi$ to indicate that we are dealing with a Łukasiewicz propositional logic.

**Remark 2.3.** Observe that $0$ corresponds to truth and any $r \in (0, 1]$ corresponds to a degree of truth or falsity, where $1$ may be construed as absolute falsity. Also observe that ‘$\dot{-}$’ plays a role analogous to that of ‘$\to$’ in classical logic: We may interpret ‘$\psi \dot{-} \varphi$’ as ‘$\psi$ *is implied by* $\varphi$,’ ‘$\varphi$ *is at least as false as* $\psi$,’ ‘$\psi$ *is at most as true as* $\varphi$,’ or simply, ‘$\psi$ *is less than or equal to* $\varphi$.’ We prefer the last interpretation.

<!-- page 5 -->

**Definition 2.4.** Let $\mathcal{S}_0 = \{P_i : i \in I\}$ be a set of distinct symbols. Let $\mathcal{S}$ be freely generated from $\mathcal{S}_0$ by the formal binary operation $\dot{-}$ and the unary operations $\neg$ and $\frac{1}{2}$. We call $\mathcal{S}$ a *continuous propositional logic*.

A truth assignment $v$ is defined as in (i) of Definition 2.2 with the extra condition that $v(\frac{1}{2}\varphi) := \frac{1}{2}v(\varphi)$. Models, satisfiability, and logical entailment are defined as in Definition 2.2. We may write $\Sigma \models^{\mathrm{CL}} \varphi$ to indicate that we are dealing with a continuous propositional logic.

## 3. AXIOMS: GROUP 1

We now present six of our fourteen axiom schemata. The first four form an axiomatization for Łukasiewicz propositional logic [Cha58, RR58].

(A1) $(\varphi \dot{-} \psi) \dot{-} \varphi$

(A2) $((\chi \dot{-} \varphi) \dot{-} (\chi \dot{-} \psi)) \dot{-} (\psi \dot{-} \varphi)$

(A3) $(\varphi \dot{-} (\varphi \dot{-} \psi)) \dot{-} (\psi \dot{-} (\psi \dot{-} \varphi))$

(A4) $(\varphi \dot{-} \psi) \dot{-} (\neg \psi \dot{-} \neg \varphi)$

When the next two axiom schemata are added to the first four (in the appropriate language), we obtain an axiomatization for continuous propositional logic [Ben].

(A5) $\frac{1}{2}\varphi \dot{-} (\varphi \dot{-} \frac{1}{2}\varphi)$

(A6) $(\varphi \dot{-} \frac{1}{2}\varphi) \dot{-} \frac{1}{2}\varphi$

Note that (A5) and (A6) say that $\frac{1}{2}$ behaves as it ought to. Informally, under the intended interpretation, (A5) and (A6) taken together imply that $\frac{1}{2}\varphi \dot{+} \frac{1}{2}\varphi = \varphi$. (‘$\dot{+}$’ may be defined by setting $\varphi \dot{+} \psi := \neg(\neg \varphi \dot{-} \psi)$; thus, according to the intended interpretation of ‘$\dot{-}$’, the interpretation of ‘$\dot{+}$’ is given by $x \dot{+} y = \min(x + y, 1)$.)

Formal deductions and the relation $\vdash$ for both logics are defined in the natural way, the only rule of inference being *modus ponens*:

$$\frac{\varphi,\quad \psi \dot{-} \varphi}{\psi}$$

We can make this more precise as follows: a *formal deduction* from $\Sigma$ is a finite sequence of formulae $(\varphi_i : i < n)$ such that for each $i < n$, either (i) $\varphi_i$ is an instance of an axiom schema, (ii) $\varphi_i \in \Sigma$, or (iii) there are $j, k < i$ such that $\varphi_k = \varphi_i \dot{-} \varphi_j$. We accordingly say that $\varphi$ is *provable from* (or *deducible from*, or *a consequence of*) $\Sigma$ and write $\Sigma \vdash \varphi$ if there is a formal deduction from $\Sigma$ ending in $\varphi$. Observe that a formula $\varphi$ is provable from $\Sigma$ just in case it is provable from a finite subset of $\Sigma$. To avoid confusion, we may write $\Sigma \vdash^{\mathrm{L}} \varphi$ to indicate that $\varphi$ is provable from $\Sigma$ in Łukasiewicz propositional logic, and

<!-- page 6 -->

*ITAÏ BEN YAACOV AND ARTHUR PAUL PEDERSEN*

we may write $\Sigma \vdash^{\mathrm{CL}} \varphi$ to indicate that $\varphi$ is provable from $\Sigma$ in continuous propositional logic. It should be fairly clear to the reader how the proof systems of continuous propositional logic and Łukasiewicz propositional logic are related. Both proof systems are of course sound, by which we mean that if $\Sigma \vdash^{\mathrm{L}} \varphi$ (respectively, $\Sigma \vdash^{\mathrm{CL}} \varphi$), then $\Sigma \models^{\mathrm{L}} \varphi$ (respectively, $\Sigma \models^{\mathrm{CL}} \varphi$). We leave this section with a definition, a few notational conventions, and a remark, each of which addresses some aspects of our presentation of continuous logic in this paper.

**Definition 3.1.** We say that a set of formulae $\Sigma$ is *inconsistent* if $\Sigma \vdash \varphi$ for every formula $\varphi$ and *consistent* otherwise.

**Notation 3.2.** Define $\psi \dot{-} n\varphi$ by recursion on $n < \omega$:

(i) $\psi \dot{-} 0\varphi := \psi$.

(ii) $\psi \dot{-} (n + 1)\varphi := (\psi \dot{-} n\varphi) \dot{-} \varphi$.

**Notation 3.3.** Let $1$ be shorthand for $\neg(\varphi \dot{-} \varphi)$, where $\varphi$ is any formula, and let $2^{-n}$ be shorthand for $\underbrace{\frac{1}{2}\cdots\frac{1}{2}}_{n\text{-times}}1$. Also, let $0$ be shorthand for $\neg 1$.

**Remark 3.4.** *Observe that on any truth assignment $v$ the set $\mathcal{D}$ generated from $1$ by applying the operations $\neg$, $\dot{-}$, and $\frac{1}{2}$ is such that $\{v(d) : d \in \mathcal{D}\} = \mathbb{D}$, the set of dyadic numbers, i.e., numbers of the form $\frac{k}{2^n}$, where $k, n < \omega$ and $k \leq 2^n$. For simplicity of notation, we do not distinguish between the syntactic set $\mathcal{D}$ thus generated and $\mathbb{D}$.*

## 4. BLACK BOX THEOREMS

We now record several results which will be used in this paper.

**Fact 4.1 (Weak Completeness for Łukasiewicz Logic [Cha59, RR58]).** *Let $\mathcal{S}$ be a Łukasiewicz propositional logic and $\varphi \in \mathcal{S}$. Then $\models \varphi$ if and only if $\vdash \varphi$.*

**Fact 4.2.** *Let $\mathcal{S}$ be a Łukasiewicz propositional logic, and $\Sigma \subseteq \mathcal{S}$. Then $\Sigma$ is consistent if and only if it is satisfiable.*

**Fact 4.3.** *Let $\mathcal{S}$ be a continuous propositional logic and $\Sigma \subseteq \mathcal{S}$. Then $\Sigma$ is consistent if and only if it is satisfiable.*

An immediate corollary of the previous fact is the following approximated form of strong completeness.

**Fact 4.4 (Approximated Strong Completeness for Continuous Logic).** *Let $\mathcal{S}$ be a continuous propositional logic, $\Sigma \subseteq \mathcal{S}$, and $\varphi \in \mathcal{S}$. Then $\Sigma \models \varphi$ if and only if $\Sigma \vdash \varphi \dot{-} 2^{-n}$ for all $n < \omega$.*

<!-- page 7 -->

In fact, this is the best we can hope for. To see why, consider $\Sigma := \{P \dot{-} 2^{-n} : n < \omega\}$. Then $\Sigma \vDash P$, yet for no finite $\Sigma_0 \subseteq \Sigma$ do we have $\Sigma_0 \vDash P$. However, we do have the following weaker result.

**Fact 4.5 (Finite Strong Completeness for Continuous Logic).** *Let $\mathcal{S}$ be a continuous propositional logic, $\Sigma \subseteq \mathcal{S}$ be finite, and $\varphi \in \mathcal{S}$. Then $\Sigma \vDash \varphi$ if and only if $\Sigma \vdash \varphi$.*

In view of the above facts, observe that if $\mathcal{S}$ is a Łukasiewicz or continuous propositional logic and $\Sigma \subseteq \mathcal{S}$,

- $\Sigma$ is inconsistent if and only if $\Sigma \vdash^{\mathrm{L}} 1$.
- $\Sigma$ is inconsistent if and only if $\Sigma \vdash^{\mathrm{CL}} d$ for some $d \in \mathbb{D} \setminus \{0\}$.

Fact 4.2 – Fact 4.5 have been established independently by the first author in [Ben]. Nonetheless, Fact 4.2 has been proved in [BC63] (indeed, for Łukasiewicz first-order logic; see also [Háj98]) and Fact 4.4 has a counterpart in [Hay63] (again, see also [Háj98]), while Fact 4.5 has been proved for rational Pavelka propositional logic [Háj98] and for Łukasiewicz propositional logic [CDM00, Háj98].

## 5. THE LANGUAGE AND SEMANTICS OF CONTINUOUS FIRST-ORDER LOGIC

**Definition 5.1.** The *logical symbols* of continuous first-order logic are

- Parentheses: $(\ ,\,)$
- Connectives: $\dot{-}$, $\neg$, $\frac{1}{2}$
- Quantifiers: sup (or inf)
- Variables: $v_0$, $v_1$, $\ldots$
- An optional binary metric: $d$

The *sup*-quantifier plays the role of the $\forall$-quantifier from classical first-order logic, whereas the *inf*-quantifier plays the role of the $\exists$-quantifier from classical first-order logic. In fact, the *sup*-quantifier can be defined in terms of the *inf*-quantifier. Furthermore, instead of an optional binary congruence relation symbol $\approx$ as in classical first-order logic, continuous first-order logic has an optional binary metric symbol $d$.

We should now say something about the choice of connectives. In classical first-order logic, a set of connectives is *complete* if every mapping from $\{0,1\}^n \to \{0,1\}$ can be written using the set of connectives. The set of connectives $\{\neg, \to\}$ is complete in this sense. Similarly, in continuous first-order logic, a set of connectives is *complete* if every continuous mapping from $[0,1]^n \to [0,1]$ can be written using the set of connectives. But this notion is much too demanding. Indeed, a complete set of connectives would require continuum many connectives. A more reasonable demand of a set of connectives is that every continuous function from $[0,1]^n \to [0,1]$ can be written using the set of connectives up to arbitrarily better approximations. A set of connectives satisfying this requirement is said to be *full* (see [BU]; see also [CDM00]). The set of connectives $\{\dot{-}, \neg, \frac{1}{2}\}$ is full in this sense, and $\{\dot{-}, \frac{1}{2}, 0, 1\}$ is full as well — so is any set of connectives which includes $\dot{-}$, $\frac{1}{2}$, and some dense set $\mathcal{C} \subseteq [0,1]$, such as $\mathbb{D}$ or $\mathbb{Q} \cap [0,1]$. Here we choose to canonize

<!-- page 8 -->

$\{\dot{-}, \neg, \frac{1}{2}\}$ as the set of connectives. As it is finite, this set of connectives is an economical choice, and it is the analogue of the popular choice of connectives $\{\neg, \to\}$ of classical first-order logic.

**Definition 5.2.** A *continuous signature* is a quadruple $\mathcal{L} = (\mathcal{R}, \mathcal{F}, \mathcal{G}, n)$ such that

(i) $\mathcal{R} \neq \emptyset$.

(ii) $\mathcal{R} \cap \mathcal{F} = \emptyset$.

(iii) $\mathcal{G}$ has the form $\{\delta_{s,i} : (0, 1] \to (0, 1] : s \in \mathcal{R} \cup \mathcal{F} \text{ and } i < n_s\}$.

(iv) $n : \mathcal{R} \cup \mathcal{F} \to \omega$.

Members of $\mathcal{R}$ are called *relation symbols*, while members of $\mathcal{F}$ are called *function symbols*. For each $s \in \mathcal{R} \cup \mathcal{F}$, we write $n_s$ for the value of $s$ under $n$ and call $n_s$ the *arity* of $s$. We call a member of $\mathcal{G}$ a *modulus of uniform continuity*.

**Remark 5.3.** Observe that members of $\mathcal{G}$ are not syntactic objects. Rather, each member of $\mathcal{G}$ is a genuine operation on $(0, 1]$. The role of the moduli of uniform continuity will be clarified below.

**Definition 5.4.** A *continuous signature with a metric* is a continuous signature with a distinguished binary relation symbol $d$.

Terms, formulae, and notions of free and bound substitution are defined in the usual way (see §6 concerning these notions). We denote the set of variables by $V$ and the set of formulae by $\mathrm{For}(\mathcal{L})$. In classical first-order logic, a metric symbol $d$ would most naturally be thought of as a function symbol. In continuous first-order logic, however, $d$ is a relation symbol, and as such, $d t_0 t_1$ is a formula rather than a term.

We write ‘$\sup_x$’ (and ‘$\inf_x$’) instead of ‘$\sup x$’ (and ‘$\inf x$’). We define ‘inf’, ‘$\wedge$’, ‘$\vee$’, and ‘$|\ |$’ by setting

$$
\begin{aligned}
\inf_x \varphi &:= \neg \sup_x \neg \varphi. \\
\varphi \wedge \psi &:= \varphi \dot{-} (\varphi \dot{-} \psi). \\
\varphi \vee \psi &:= \neg(\neg \varphi \wedge \neg \psi). \\
|\varphi - \psi| &:= (\varphi \dot{-} \psi) \vee (\psi \dot{-} \varphi).
\end{aligned}
$$

The reader should verify that the definition of ‘inf’ accords with the obvious intended interpretation when the semantics are given below. Observe that (A2) becomes ‘$(\varphi \wedge \psi) \dot{-} (\psi \wedge \varphi)$.’ Also, according to the intended interpretation of ‘$\dot{-}$,’ the interpretation of ‘$\wedge$’ is given by $x \wedge y = \min(x, y)$. Thus, according to the interpretation of ‘$\wedge$,’ the interpretation of ‘$\vee$’ is given by $x \vee y = \max(x, y)$, whereby the interpretation of ‘$|\ |$’ is one-dimensional Euclidean distance. As $0$ corresponds to truth, it should be clear that the interpretation of ‘$\wedge$’ is the continuous analogue of the classical ‘or,’ whereas the interpretation of ‘$\vee$’ is the continuous analogue of the classical ‘and.’

**Definition 5.5.**

<!-- page 9 -->

(i) Let $(M, d)$ and $(M', d')$ be metric spaces and $f : M \to M'$ be a function. We say that $\delta : (0, 1] \to (0, 1]$ is a *modulus of uniform continuity for $f$* if for each $\epsilon \in (0, 1]$ and all $a, b \in M$, $d(a, b) < \delta(\epsilon) \implies d'(f(a), f(b)) \le \epsilon$.

(ii) We say that $f$ is *uniformly continuous* if there is a modulus of uniform continuity for $f$.

**Definition 5.6.** Let $\mathcal{L}$ be a continuous signature. A *continuous $\mathcal{L}$-pre-structure* is an ordered pair $\mathfrak{M} = (M, \rho)$, where $M$ is a non-empty set and $\rho$ is a function whose domain is $\mathcal{R} \cup \mathcal{F}$, such that:

(i) To each $f \in \mathcal{F}$, $\rho$ assigns a mapping $f^{\mathfrak{M}} : M^{n_f} \to M$.

(ii) To each $P \in \mathcal{R}$, $\rho$ assigns a mapping $P^{\mathfrak{M}} : M^{n_P} \to [0, 1]$.

If $\mathcal{L}$ is also a continuous signature with a metric, then $\mathfrak{M}$ is such that:

(iii) $\rho$ assigns to $d$ a pseudo-metric $d^{\mathfrak{M}} : M \times M \to [0, 1]$.

(iv) For each $f \in \mathcal{F}$, $i < n_f$, and $\epsilon \in (0, 1]$, $\delta_{f,i}$ satisfies the following condition:

$$\forall \bar{a}, \bar{b}, c, e\,[d^{\mathfrak{M}}(c, e) < \delta_{f,i}(\epsilon) \implies d^{\mathfrak{M}}(f^{\mathfrak{M}}(\bar{a}, c, \bar{b}), f^{\mathfrak{M}}(\bar{a}, e, \bar{b})) \le \epsilon],$$

where $|\bar{a}| = i$ and $|\bar{a}| + |\bar{b}| + 1 = n_f$; we thereby call $\delta_{f,i}$ the *uniform continuity modulus of $f$ with respect to the $i$th argument*.

(v) For each $P \in \mathcal{R}$, $i < n_P$, and $\epsilon \in (0, 1]$, $\delta_{P,i}$ satisfies the following condition:

$$\forall \bar{a}, \bar{b}, c, e\,[d^{\mathfrak{M}}(c, e) < \delta_{P,i}(\epsilon) \implies \max(P^{\mathfrak{M}}(\bar{a}, c, \bar{b}) - P^{\mathfrak{M}}(\bar{a}, e, \bar{b}), 0) \le \epsilon],$$

where $|\bar{a}| = i$ and $|\bar{a}| + |\bar{b}| + 1 = n_P$; we thereby call $\delta_{P,i}$ the *uniform continuity modulus of $P$ with respect to the $i$th argument*.

Here, as well as in the remainder of this paper, a tuple $a_0, \ldots, a_{n-1}$ may for convenience be denoted by $\bar{a}$, whereby $|\bar{a}|$ will denote the length of $\bar{a}$.

**Convention 5.7.** In this paper we make the convention that for an $n$-ary function $f$, the $i$th argument of the expression $f(x_0, \ldots, x_{n-1})$ is $x_i$. In particular, the $0$th argument of $f$ is $x_0$.

**Remark 5.8.** Conditions (iv) and (v) correspond to the congruence axioms of classical first-order logic. In classical first-order logic it is required that a distinguished binary relation symbol $\approx$ be such that for each classical structure $\mathfrak{A}$, the relation $\approx^{\mathfrak{A}}$ is an equivalence relation satisfying the following congruence axioms:

- For each function symbol $f$ and $i < n_f$,

$$\forall \bar{a}, \bar{b}, c, e\,(c \approx^{\mathfrak{A}} e \implies f^{\mathfrak{A}}(\bar{a}, c, \bar{b}) \approx^{\mathfrak{A}} f^{\mathfrak{A}}(\bar{a}, e, \bar{b})),$$

where $|\bar{a}| = i$ and $|\bar{a}| + |\bar{b}| + 1 = n_f$.

- For each relation symbol $P$ and $i < n_P$,

$$\forall \bar{a}, \bar{b}, c, e\,(c \approx^{\mathfrak{A}} e \implies (P^{\mathfrak{A}}(\bar{a}, c, \bar{b}) \Rightarrow P^{\mathfrak{A}}(\bar{a}, e, \bar{b}))),$$

where $|\bar{a}| = i$ and $|\bar{a}| + |\bar{b}| + 1 = n_P$.

In classical first-order logic, one can thereby show that for each classical structure $\mathfrak{A}$, the relation $\approx^{\mathfrak{A}}$ satisfies the following properties:

<!-- page 10 -->

- For each function symbol $f$,

$$\forall \bar{a}, \bar{b}\,\left(\left(\bigwedge_{i < n_f} a_i \approx^{\mathfrak{A}} b_i\right) \Longrightarrow f^{\mathfrak{A}}(\bar{a}) \approx^{\mathfrak{A}} f^{\mathfrak{A}}(\bar{b})\right),$$

where $|\bar{a}| = |\bar{b}| = n_f$.

- For each relation symbol $P$,

$$\forall \bar{a}, \bar{b}\,\left(\left(\bigwedge_{i < n_P} a_i \approx^{\mathfrak{A}} b_i\right) \Longrightarrow \left(P^{\mathfrak{A}}(\bar{a}) \Rightarrow P^{\mathfrak{A}}(\bar{b})\right)\right),$$

where $|\bar{a}| = |\bar{b}| = n_P$.

Along a similar vein, in continuous first-order logic one can show that for each function symbol $f$ and predicate symbol $P$, there are moduli of uniform continuity $\Delta_f$ and $\Delta_P$ which depend on their uniform continuity moduli $(\delta_{f,i} : i < n_f)$ and $(\delta_{P,i} : i < n_P)$, respectively. For example, $\Delta_f : (0, 1] \to (0, 1]$ may be defined by setting $\Delta_f(\epsilon) := \min\{\delta_{f,0}(\epsilon/n_f), \ldots, \delta_{f,n_f-1}(\epsilon/n_f)\}$. Accordingly, in each continuous $\mathcal{L}$-pre-structure $\mathfrak{M}$, the mapping $\Delta_f$ is a modulus of uniform continuity for $f^{\mathfrak{M}}$ with respect to the maximum metric $D_{n_f}^{\mathfrak{M}}$ defined by $D_{n_f}^{\mathfrak{M}}(\bar{a}, \bar{b}) := \max_{i < n_f}(d^{\mathfrak{M}}(a_i, b_i)) = \bigvee_{i < n_f} d^{\mathfrak{M}}(a_i, b_i)$. This may be expressed formally as follows:

- For each $f \in \mathcal{F}$ and $\epsilon \in (0, 1]$, $\Delta_f$ satisfies the following condition:

$$\forall \bar{a}, \bar{b}\,\left[\left(\bigvee_{i < n_f} d^{\mathfrak{M}}(a_i, b_i)\right) < \Delta_f(\epsilon) \Longrightarrow d^{\mathfrak{M}}(f^{\mathfrak{M}}(\bar{a}), f^{\mathfrak{M}}(\bar{b})) \le \epsilon\right],$$

where $|\bar{a}| = |\bar{b}| = n_f$.

In light of the foregoing discussion, observe that for every continuous $\mathcal{L}$-pre-structure $\mathfrak{M}$ and $s \in \mathcal{R} \cup \mathcal{F}$, $s^{\mathfrak{M}}$ is a uniformly continuous function.

**Definition 5.9.** A *continuous $\mathcal{L}$-structure* is a continuous $\mathcal{L}$-pre-structure $\mathfrak{M} = (M, \rho)$ such that $\rho$ assigns to $d$ a *complete metric*:

(i) $\forall a, b\,(d^{\mathfrak{M}}(a, b) = 0 \Longrightarrow a = b)$.

(ii) Every Cauchy sequence converges.

**Definition 5.10.**

(i) If $\mathfrak{M}$ is a continuous $\mathcal{L}$-pre-structure, then an *$\mathfrak{M}$-assignment* is a mapping $\sigma : V \to M$.

(ii) If $\sigma$ is an $\mathfrak{M}$-assignment, $x \in V$, and $a \in M$, we define an $\mathfrak{M}$-assignment $\sigma_x^a$ by setting for all $y \in V$,

$$\sigma_x^a(y) := \begin{cases} a & \text{if } x = y \\ \sigma(y) & \text{otherwise.} \end{cases}$$

The interpretation of a term $t$ in a continuous $\mathcal{L}$-pre-structure $\mathfrak{M}$ is defined as in classical first-order logic. We denote its interpretation by $t^{\mathfrak{M}, \sigma}$.

**Definition 5.11.** Let $\mathfrak{M}$ be a continuous $\mathcal{L}$-pre-structure. For a formula $\varphi$ and an $\mathfrak{M}$-assignment $\sigma$, we define *the value of $\varphi$ in $\mathfrak{M}$ under $\sigma$*, $\mathfrak{M}(\varphi, \sigma)$, by induction:

(i) $\mathfrak{M}(P t_0 \cdots t_{n_P-1}, \sigma) := P^{\mathfrak{M}}(t_0^{\mathfrak{M}, \sigma}, \ldots, t_{n_P-1}^{\mathfrak{M}, \sigma})$.

(ii) $\mathfrak{M}(\alpha \dot{-} \beta, \sigma) := \max(\mathfrak{M}(\alpha, \sigma) - \mathfrak{M}(\beta, \sigma), 0)$.

(iii) $\mathfrak{M}(\neg \alpha, \sigma) := 1 - \mathfrak{M}(\alpha, \sigma)$.

<!-- page 11 -->

(iv) $\mathfrak{M}(\frac{1}{2}\alpha, \sigma) := \frac{1}{2}\mathfrak{M}(\alpha, \sigma)$.

(v) $\mathfrak{M}(\sup_x \alpha, \sigma) := \sup\{\mathfrak{M}(\alpha, \sigma_x^a) : a \in M\}$.

If one chooses to use ‘inf’ instead of ‘sup,’ one may replace (v) with $\mathfrak{M}(\inf_x \alpha, \sigma) := \inf\{\mathfrak{M}(\alpha, \sigma_x^a) : a \in M\}$.

**Definition 5.12.** Let $\mathfrak{M}$ be a continuous $\mathcal{L}$-pre-structure, let $\sigma$ be an $\mathfrak{M}$-assignment, and let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$.

(i) We say that $(\mathfrak{M}, \sigma)$ *models* (or *satisfies*) $\Gamma$ and that $(\mathfrak{M}, \sigma)$ is a *model* of $\Gamma$, written $(\mathfrak{M}, \sigma) \vDash_Q \Gamma$, if $\mathfrak{M}(\varphi, \sigma) = 0$ for all $\varphi \in \Gamma$. We of course say that $(\mathfrak{M}, \sigma)$ is a model of $\varphi$ and write $(\mathfrak{M}, \sigma) \vDash_Q \varphi$ if $(\mathfrak{M}, \sigma) \vDash_Q \{\varphi\}$.

(ii) We say that $\Gamma$ is *satisfiable* if it has a model.

**Definition 5.13.** Let $\Gamma$ be a set of formulae and $\varphi$ be a formula. We write $\Gamma \vDash_Q \varphi$ if every model of $\Gamma$ is a model of $\varphi$. If $\emptyset \vDash_Q \varphi$, we say that $\varphi$ is *valid*.

**Definition 5.14.** We write $\varphi \equiv \psi$ if $\mathfrak{M}(\varphi, \sigma) = \mathfrak{M}(\psi, \sigma)$ for every continuous $\mathcal{L}$-pre-structure and $\mathfrak{M}$-assignment $\sigma$.

With these definitions, many properties analogous to those of classical first-order logic can be derived (see [EFT94]).

## 6. Substitution and Metric Completions

**Substitution.** As in classical first-order logic, *free* and *bound* substitution play an important role in connecting the syntax with the semantics. This brief subsection is intended to remind the reader of these two notions of substitution and to indicate to the reader what features of these notions are crucial for our purposes.

**Definition 6.1.** Let $t$ be a term, and let $x$ be a variable. We define the *free substitution* of $t$ for $x$ inside a formula $\varphi$, $\varphi[t/x]$, as the result of replacing $x$ by $t$ in $\varphi$ if $x$ occurs free in $\varphi$. We say that $\varphi[t/x]$ is *correct* if no variable $y$ in $t$ is captured by a $\sup_y$ (or $\inf_y$) quantifier in $\varphi[t/x]$.

The next lemma is the continuous analogue of the substitution lemma of classical first-order logic.

**Lemma 6.2** (*Substitution Lemma*). Let $\mathfrak{M}$ be a continuous $\mathcal{L}$-pre-structure, and let $\sigma$ be an $\mathfrak{M}$-assignment. Let $t$ be a term, $x$ be a variable, and $\varphi$ be a formula. Put $a := t^{\mathfrak{M}, \sigma}$. Suppose $\varphi[t/x]$ is correct. Then

$$\mathfrak{M}(\varphi[t/x], \sigma) = \mathfrak{M}(\varphi, \sigma_x^a).$$

**Definition 6.3.** Let $\varphi$ be a formula, and let $x$, $y$ be variables. We define the *bound substitution* of $y$ for $x$ inside $\varphi$, $\varphi\{y/x\}$, as the result of replacing each subformula $\sup_x \alpha$ (or $\inf_x \alpha$) of $\varphi$ by $\sup_y \alpha[y/x]$ (or $\inf_y \alpha$). We say that $\varphi\{y/x\}$ is *correct* if $y$ is not free in $\alpha$ and $\alpha[y/x]$ is correct in each such subformula $\sup_x \alpha$ (or $\inf_x \alpha$).

<!-- page 12 -->

The following lemma is an immediate result. The reader interested may consult [EFT94] for a classical first-order proof to see how a proof for continuous first-order logic may be constructed.

**Lemma 6.4 (Bound Substitution Lemma).** *Let $\varphi$ be a formula, and let $x_0, \dots, x_{n-1}$ be a finite sequence of variables. Then by a sequence of bound substitutions there is a formula $\varphi'$ in which $x_0, \dots, x_{n-1}$ are not bound and $\varphi \equiv \varphi'$.*

**Metric Completions.** We will presently see that each continuous $\mathcal{L}$-pre-structure (for a continuous signature with a metric) is virtually indistinguishable from its metric completion (Theorem 6.9). To this end, we first offer a definition.

**Definition 6.5.** Let $\mathfrak{M}$ and $\mathfrak{N}$ be continuous $\mathcal{L}$-pre-structures, and let $h : M \to N$. We call $h$ an $\mathcal{L}$-morphism of $\mathfrak{M}$ into $\mathfrak{N}$ if $h$ satisfies the following two conditions:

(i) For each $f \in \mathcal{F}$ and all $a_0, \dots, a_{n_f-1} \in M$,
$$h(f^{\mathfrak{M}}(a_0, \dots, a_{n_f-1})) = f^{\mathfrak{N}}(h(a_0), \dots, h(a_{n_f-1})).$$

(ii) For each $P \in \mathcal{R}$ and all $a_0, \dots, a_{n_P-1} \in M$,
$$P^{\mathfrak{M}}(a_0, \dots, a_{n_P-1}) = P^{\mathfrak{N}}(h(a_0), \dots, h(a_{n_P-1})).$$

We call $h$ an *elementary $\mathcal{L}$-morphism* if $h$ is an $\mathcal{L}$-morphism and for every $\mathfrak{M}$-assignment $\sigma$ and formula $\varphi$, $\mathfrak{M}(\varphi, \sigma) = \mathfrak{N}(\varphi, h \circ \sigma)$.

Observe that if $\mathcal{L}$ is a continuous signature with a metric $d$ and $h$ is an $\mathcal{L}$-morphism of $\mathfrak{M}$ into $\mathfrak{N}$, then for all $a_0, a_1 \in M$,
$$d^{\mathfrak{M}}(a_0, a_1) = d^{\mathfrak{N}}(h(a_0), h(a_1)).$$
In other words, $h$ is an isometry.

An immediate consequence of our definitions is the following theorem.

**Theorem 6.6.** *If $\mathfrak{M}$ and $\mathfrak{N}$ are continuous $\mathcal{L}$-pre-structures and $h : M \to N$ is a surjective $\mathcal{L}$-morphism, then $h$ is an elementary $\mathcal{L}$-morphism of $\mathfrak{M}$ onto $\mathfrak{N}$.*

*Proof.* Straightforward induction on formulae. $\square$

**Definition 6.7.** Let $\mathfrak{M}$ be a continuous $\mathcal{L}$-pre-structure. Let $t$ be a term and $\varphi$ be a formula such that all variables occurring in $t$ and all free variables occurring in $\varphi$ appear among $n$ distinct variables $x_0, \dots, x_{n-1}$. Define functions $\widetilde{t}^{\mathfrak{M}, \bar{x}} : M^n \to M$ and $\widetilde{\varphi}^{\mathfrak{M}, \bar{x}} : M^n \to [0, 1]$ by setting for all $\bar{a} \in M^n$,
$$\widetilde{t}^{\mathfrak{M}, \bar{a}} := t^{\mathfrak{M}, \sigma}$$
$$\widetilde{\varphi}^{\mathfrak{M}, \bar{x}}(\bar{a}) := \mathfrak{M}(\varphi, \sigma),$$
where $\sigma$ is an $\mathfrak{M}$-assignment such that $\sigma(x_i) = a_i$ for each $i < n$.

We have all of the ingredients necessary to prove the following theorem.

<!-- page 13 -->

**Theorem 6.8.** Let $\mathfrak{M}$ be a continuous $\mathcal{L}$-pre-structure. Then for every term $t$ and formula $\varphi$ the mappings $\tilde{t}^{\mathfrak{M}, \bar{x}} : M^n \to M$ and $\tilde{\varphi}^{\mathfrak{M}, \bar{x}} : M^n \to [0, 1]$ are uniformly continuous.

*Proof.* By induction on terms and formulae, using the fact that moduli of uniform continuity can be built up from other moduli, as mentioned in Remark 5.8. $\square$

Using Lemma 6.4, Theorem 6.6, and Theorem 6.8, one can prove the following:

**Theorem 6.9 (Existence of Metric Completion).** *Let $\mathcal{L}$ be a continuous signature with a metric, and let $\mathfrak{M}$ be a continuous $\mathcal{L}$-pre-structure. Then there is a continuous $\mathcal{L}$-structure $\widehat{\mathfrak{M}}$ and an elementary $\mathcal{L}$-morphism of $\mathfrak{M}$ into $\widehat{\mathfrak{M}}$.*

*Proof.* The proof invokes elementary facts about metric spaces, pseudo-metrics, Cauchy sequences, and metric completions. Essential to this proof is the fact that for all metric spaces $(M, d)$ and $(M', d')$ such that $(M', d')$ is complete and $N \subseteq M$, if $f : N \to M'$ is a mapping and $\delta$ is a modulus of uniform continuity for $f$, then $f$ can be uniquely extended to a function $\bar{f} : \bar{N} \to M'$ such that $\delta$ is a modulus of uniform continuity for $\bar{f}$ (where $\bar{N}$ denotes the closure of $N$ in $M$). This fact is important insofar as it implies that an underlying continuous signature with a metric will not have to be altered for a metric completion. $\square$

**Definition 6.10.** Let $\mathcal{L}$ be a continuous signature with a metric, let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$, and let $\varphi$ be a formula.

(i) We write $\Gamma \vDash_{QC} \varphi$ if for every continuous $\mathcal{L}$-structure $\mathfrak{M}$ and $\mathfrak{M}$-assignment $\sigma$, if $(\mathfrak{M}, \sigma) \vDash_Q \Gamma$, then $(\mathfrak{M}, \sigma) \vDash_Q \varphi$.

(ii) We say that $\Gamma$ is *completely satisfiable* or that $\Gamma$ has a *complete model* if there is a continuous $\mathcal{L}$-structure $\mathfrak{M}$ and $\mathfrak{M}$-assignment $\sigma$ such that $(\mathfrak{M}, \sigma)$ models $\Gamma$.

We therefore have the following corollary:

**Corollary 6.11.** *Let $\mathcal{L}$ be a continuous signature with a metric, and let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$. Then for every formula $\varphi$,*

(i) $\Gamma \vDash_Q \varphi$ *if and only if* $\Gamma \vDash_{QC} \varphi$.

(ii) $\Gamma$ *is satisfiable if and only if* $\Gamma$ *is completely satisfiable.*

We may thereby restrict the notion of logical entailment to continuous $\mathcal{L}$-structures.

In classical first-order logic, if one were to require a distinguished binary relation symbol $\approx$ be interpreted only as a congruence relation in each classical structure rather than as strict equality, then one could show for each such structure that there is a surjective elementary $\mathcal{L}$-morphism (in the obvious sense) onto its quotient structure. Accordingly, we would find that classical first-order logic does not distinguish between structures which require that $\approx$ be interpreted as a congruence relation and structures which require that $\approx$ be interpreted as strict equality.

In continuous first-order logic, we see a somewhat analogous result. We require that a distinguished binary relation symbol $d$ be interpreted as a pseudo-metric that satisfies

<!-- page 14 -->

congruence properties, akin to those of classical first-order logic (cf. Definition 5.6, parts (iii) and (iv)). One can show that for each $\mathcal{L}$-pre-structure, there is a surjective elementary $\mathcal{L}$-morphism onto its quotient structure (which essentially transforms $d$ into a genuine metric). Yet one can go one step further: For any $\mathcal{L}$-pre-structure with a genuine metric, there is an injective elementary $\mathcal{L}$-morphism (and *a fortiori* an isometry) into its completion, a continuous $\mathcal{L}$-structure. Therefore, continuous first-order logic does not distinguish between continuous $\mathcal{L}$-pre-structures and continuous $\mathcal{L}$-structures. Theorem 6.9 can be seen as encoding this fact. As you would expect, most of our work does not rely on this fact, but it nevertheless indicates what matters.

## 7. AXIOMS: GROUP 2

Before we present the second group of axioms, let us define a notion familiar from classical first-order logic. We say that a formula $\varphi$ is a *generalization* of a formula $\psi$ if for some $n < \omega$ there are variables $x_1, \ldots, x_n$ such that $\varphi = \sup_{x_1} \cdots \sup_{x_n} \psi$ (see [End01]). Observe that every formula is a generalization of itself.

When all generalizations of the following eight axiom schemata are added to all generalizations of (A1)–(A6) (in the appropriate language of course), we obtain an axiomatization for continuous first-order logic. In this article we show that this axiomatization is complete. Formal deductions and provability are defined as in §3, the only rule of inference again being *modus ponens*. We write $\Gamma \vdash_Q \varphi$ to indicate that $\varphi$ is provable from $\Gamma$ in continuous first-order logic. Recall that a formula $\varphi$ is provable from $\Gamma$ just in case it is provable from a finite subset of $\Gamma$.

The first three schemata are analogues of axiom schemata of classical first-order logic (see [End01]).

(A7) $(\sup_x \psi \dot{-} \sup_x \varphi) \dot{-} \sup_x (\psi \dot{-} \varphi)$

(A8) $\varphi[t/x] \dot{-} \sup_x \varphi$, where substitution is correct

(A9) $\sup_x \varphi \dot{-} \varphi$, where $x$ is not free in $\varphi$

If we are dealing with a continuous signature with a metric, we add:

(A10) $dxx$

(A11) $dxy \dot{-} dyx$

(A12) $(dxz \dot{-} dxy) \dot{-} dyz$

(A13) For each $f \in \mathcal{F}$, $\epsilon \in (0, 1]$, and $r, q \in \mathbb{D}$ with $r > \epsilon$ and $q < \delta_{f,i}(\epsilon)$, the following is an axiom (where $|\bar{x}| = i$ and $|\bar{x}| + |\bar{y}| + 1 = n_f$):

$$(q \dot{-} dzw) \wedge (df\bar{x}z\bar{y}f\bar{x}w\bar{y} \dot{-} r)$$

<!-- page 15 -->

**A PROOF OF COMPLETENESS**

(A14) For each $P \in \mathcal{R}$, $\epsilon \in (0, 1]$, and $r, q \in \mathbb{D}$ with $r > \epsilon$ and $q < \delta_{P,i}(\epsilon)$, the following is an axiom (where $|\bar{x}| = i$ and $|\bar{x}| + |\bar{y}| + 1 = n_P$):

$$(q \dot{-} dzw) \wedge ((P\bar{x}z\bar{y} \dot{-} P\bar{x}w\bar{y}) \dot{-} r)$$

Axiom schemata (A10) – (A12) assert that $d$ is a pseudo-metric. These axiom schemata correspond to the equivalence relation axiom schemata of classical first-order logic. Although less immediate, (A13) – (A14) define the uniform continuity moduli with respect to the $i$th argument.

Let us informally consider (A13). Suppose (A13) holds and that $d(z,w) < \delta_{f,i}(\epsilon)$. Then there is $q \in \mathbb{D}$ such that $d(z,w) < q < \delta_{f,i}(\epsilon)$, so $q \dot{-} d(z,w) > 0$, whence by (A13) it follows that $d(f(\bar{x},z,\bar{y}), f(\bar{x},w,\bar{y})) \dot{-} r = 0$, i.e., $d(f(\bar{x},z,\bar{y}), f(\bar{x},w,\bar{y})) \leq r$ for every $r > \epsilon$. Thus, $d(f(\bar{x},z,\bar{y}), f(\bar{x},w,\bar{y})) \leq \epsilon$, so $\delta_{f,i}$ is a uniform continuity modulus of $f$ with respect to the $i$th argument. Conversely, suppose $\delta_{f,i}$ is a uniform continuity modulus of $f$ with respect to the $i$th argument and that $r, q \in \mathbb{D}$ are such that $r > \epsilon$ and $q < \delta_{f,i}(\epsilon)$. On the one hand, if $q \dot{-} d(z,w) > 0$, then $d(z,w) < q < \delta_{f,i}(\epsilon)$ and so $d(f(\bar{x},z,\bar{y}), f(\bar{x},w,\bar{y})) \leq \epsilon < r$, whence $d(f(\bar{x},z,\bar{y}), f(\bar{x},w,\bar{y})) \dot{-} r = 0$ and therefore $(q \dot{-} d(z,w)) \wedge (d(f(\bar{x},z,\bar{y}), f(\bar{x},w,\bar{y})) \dot{-} r) = 0$. On the other hand, if $q \dot{-} d(z,w) \leq 0$, again we have $(q \dot{-} d(z,w)) \wedge (d(f(\bar{x},z,\bar{y}), f(\bar{x},w,\bar{y})) \dot{-} r) = 0$.

**Remark 7.1.** In view of Remark 5.8, the reader may have noticed that a continuous signature could equivalently be defined so that $\mathcal{G}$ may instead have the form $\{\delta_s : (0, 1] \to (0, 1] : s \in \mathcal{R} \cup \mathcal{F}\}$, whereby one could forgo talk of moduli of uniform continuity of each symbol $s$ with respect to each of its arguments. In particular, (A13) could be replaced by

(A13′) For every $\epsilon \in (0, 1]$ and $r, q \in \mathbb{D}$ with $r > \epsilon$ and $q < \Delta_f(\epsilon)$, the following is an axiom:

$$(q \dot{-} \bigvee_{i < n_f} dx_i y_i) \wedge (dfx_0 \cdots x_{n_f-1} fy_0 \cdots y_{n_f-1} \dot{-} r)$$

(A14) could also be replaced by an analogous axiom. Situations might arise in which the uniform continuity moduli of a symbol with respect to each of its arguments are very different, and one might desire to keep track of this, thereby preferring one definition over the other.

We conclude this section with a soundness theorem.

**Theorem 7.2 (Soundness).** Let $\mathcal{L}$ be a continuous signature (with a metric), and let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$. Then for every formula $\varphi$,

(i) If $\Gamma \vdash_Q \varphi$, then $\Gamma \vDash_Q \varphi$ ($\Gamma \vDash_{QC} \varphi$).

(ii) If $\Gamma$ is (completely) satisfiable, then $\Gamma$ is consistent.

*Proof.* It suffices to show that each axiom schema is valid. The facts recorded in §4 can be used to show that (A1) – (A6) are valid, while the results from §6 can be used to prove that (A7) – (A9) are valid. The discussion following (A14) explains why (A10) – (A14) are valid. $\square$

<!-- page 16 -->

**8. THE ESSENTIALS**

In this section, we rely heavily on facts recorded in §4 insofar as we exploit obvious relations amongst continuous first-order logic and continuous and Łukasiewicz propositional logics.

**The Deduction Theorem, Generalization Theorem, and a Lemma about Bound Substitution.** Observe

$$
\{(P \dot{-} Q) \dot{-} Q,\, Q\} \vdash^{\mathrm{L}} P, \text{ but}
$$

$$
\{(P \dot{-} Q) \dot{-} Q\} \nvdash^{\mathrm{L}} P \dot{-} Q.
$$

Thus the reader should be unsurprised to find that continuous first-order logic only satisfies a weak version of the classical Deduction Theorem.

**Theorem 8.1 (Deduction Theorem).** Let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$, and let $\varphi$, $\psi$ be formulae. Then $\Gamma \cup \{\psi\} \vdash_Q \varphi$ if and only if $\Gamma \vdash_Q \varphi \dot{-} n\psi$ for some $n < \omega$.

*Proof.* Right to left is clear. For the implication from left to right, observe that for all $\alpha$, $\beta$, $\gamma$ and $n$, $m < \omega$,

$$
\vdash^{\mathrm{L}} \bigl((\beta \dot{-} (n+m)\alpha) \dot{-} ((\beta \dot{-} \gamma) \dot{-} n\alpha)\bigr) \dot{-} (\gamma \dot{-} m\alpha).
$$

This can be shown using the semantics of Łukasiewicz propositional logic. The proof then proceeds by induction on the set of consequences of $\Gamma \cup \{\psi\}$. $\square$

**Lemma 8.2 (Generalization Theorem).** Let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$, and let $\varphi$ be a formula. If $\Gamma \vdash \varphi$ and $x$ is not a free variable in $\Gamma$, then $\Gamma \vdash \sup_x \varphi$.

*Proof.* This is similar to the proof of the Generalization Theorem for classical first-order logic (see [End01]). $\square$

To illustrate how we rely on facts recorded in §4, we provide a proof of the next lemma.

**Lemma 8.3.** Let $\varphi$ be a formula, and let $y$ be a variable which does not occur in $\varphi$. Then

(a) $\vdash_Q \varphi \dot{-} \varphi\{y/x\}$.

(b) $\vdash_Q \varphi\{y/x\} \dot{-} \varphi$.

*Proof.* This is proved by induction on $\varphi$ for $y$ which does not occur in $\varphi$.

$\varphi = P t_0 \cdots t_{n_P-1}$: Then by definition $\varphi\{y/x\} = \varphi$; since $\vdash_Q \varphi \dot{-} \varphi$, we are done.

$\varphi = \frac{1}{2}\psi$: Then by definition $\varphi\{y/x\} = \frac{1}{2}\psi\{y/x\}$ and this bound substitution is correct. So by the induction hypothesis, we have $\vdash_Q \psi \dot{-} \psi\{y/x\}$ and $\vdash_Q \psi\{y/x\} \dot{-} \psi$. Now observe

$$
\vdash^{\mathrm{CL}} \tfrac{1}{2}\alpha \dot{-} \alpha, \text{ and}
$$

$$
\vdash^{\mathrm{CL}} \left(\tfrac{1}{2}\beta \dot{-} \tfrac{1}{2}\alpha\right) \dot{-} \tfrac{1}{2}(\beta \dot{-} \alpha).
$$

<!-- page 17 -->

## A PROOF OF COMPLETENESS

Thus by a few applications of *modus ponens*, we arrive at (a) and (b).

$\varphi = \neg\psi$: Then again by definition $\varphi\{y/x\} = \neg\psi\{y/x\}$ and this bound substitution is correct. Observe

$$
\vdash^L (\neg\alpha \dot{-} \neg\beta) \dot{-} (\beta \dot{-} \alpha).
$$

Using the induction hypothesis and *modus ponens* we obtain (a) and (b).

$\varphi = (\beta \dot{-} \alpha)$: Then $\varphi\{y/x\} = (\beta\{y/x\} \dot{-} \alpha\{y/x\})$ and $\beta\{y/x\}$ and $\alpha\{y/x\}$ are correct. Our induction hypothesis supplies us

$$
\vdash_Q \alpha \dot{-} \alpha\{y/x\},
$$

$$
\vdash_Q \alpha\{y/x\} \dot{-} \alpha,
$$

and

$$
\vdash_Q \beta \dot{-} \beta\{y/x\},
$$

$$
\vdash_Q \beta\{y/x\} \dot{-} \beta.
$$

Moreover, observe

$$
\vdash^L (((\beta' \dot{-} \alpha') \dot{-} (\beta \dot{-} \alpha)) \dot{-} (\beta' \dot{-} \beta)) \dot{-} (\alpha \dot{-} \alpha').
$$

Hence, by repeated applications of *modus ponens* and the induction hypothesis, we obtain (a) and (b).

$\varphi = \sup_x \psi$: Then $\varphi\{y/x\} = \sup_x \psi[y/x]$ and this substitution is correct ($y$ is not free in $\psi$). Hence,

1. $\vdash_Q \psi[y/x] \dot{-} \sup_x \psi$ (A8)
2. $\vdash_Q \sup_y(\psi[y/x] \dot{-} \sup_x \psi)$ (Generalization Theorem)
3. $\vdash_Q (\sup_y \psi[y/x] \dot{-} \sup_y \sup_x \psi) \dot{-} \sup_y(\psi[y/x] \dot{-} \sup_x \psi)$ (A7)
4. $\vdash_Q \sup_y \psi[y/x] \dot{-} \sup_y \sup_x \psi$ (*modus ponens*)
5. $\vdash_Q ((\sup_y \psi[y/x] \dot{-} \sup_x \psi) \dot{-} (\sup_y \psi[y/x] \dot{-} \sup_y \sup_x \psi)) \dot{-} (\sup_y \sup_x \psi \dot{-} \sup_x \psi)$ (A2)
6. $\vdash_Q \sup_y \sup_x \psi \dot{-} \sup_x \psi$ (A9) ($y$ is not free in $\sup_x \psi$),

from which it follows by applying *modus ponens* several times that $\vdash_Q \varphi\{y/x\} \dot{-} \varphi$. A similar argument can be used to establish (a).

$\varphi = \sup_z \psi$ and $z \neq x$: Then $\varphi\{y/x\} = \sup_z \psi\{y/x\}$ and this bound substitution is correct. Apply the induction hypothesis, the Generalization Theorem, (A7), and *modus ponens* to obtain (a) and (b). $\square$

If $c$ is an $0$-ary function symbol (what we of course call a *constant symbol*) and $x$ is a variable, we may define $\varphi[x/c]$ in the expected way. However, we omit a formal definition and state a lemma without proof.

**Lemma 8.4.** *Let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$, and let $\varphi$ be a formula. If $\Gamma \vdash_Q \varphi$, $c$ is a constant symbol that does not occur in $\Gamma$, and $x$ does not occur in $\varphi$, then $\Gamma \vdash_Q \sup_x \varphi[x/c]$.*

<!-- page 18 -->

**Maximal Consistent Sets of Formulae.** In classical first-order logic, we say that a set $\Delta$ of formulae is *maximal consistent* if $\Delta$ is consistent and for every formula $\varphi$, $\varphi \in \Delta$ or $\neg\varphi \in \Delta$.

In continuous first-order, however, this definition will not do. For we certainly should like to exclude *both* $\frac{1}{2}$ and $\neg\frac{1}{2}$ from *every* consistent set. In this subsection, we show what one *should* mean by calling a set of formulae maximal consistent in continuous first-order logic.

**Lemma 8.5.** Let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$ be consistent. Then for all formulae $\varphi$, $\psi$,

(i) If $\Gamma \vdash_Q \varphi \dot{-} 2^{-n}$ for all $n < \omega$ then $\Gamma \cup \{\varphi\}$ is consistent.

(ii) Either $\Gamma \cup \{\varphi \dot{-} \psi\}$ or $\Gamma \cup \{\psi \dot{-} \varphi\}$ is consistent.

*Proof.*

(i) Suppose $\Gamma \vdash_Q \varphi \dot{-} 2^{-n}$ for all $n < \omega$. For *reductio ad absurdum*, assume $\Gamma \cup \{\varphi\}$ is inconsistent. Then by the Deduction Theorem, $\Gamma \vdash 1 \dot{-} m\varphi$ for some $m < \omega$. Observe

$$
\vdash^{\mathrm{L}} (((\beta \dot{-} \alpha_{\sigma(0)}) \dot{-} \alpha_{\sigma(1)}) \dot{-} \cdots \dot{-} \alpha_{\sigma(k-1)}) \dot{-} (((\beta \dot{-} \alpha_0) \dot{-} \alpha_1) \dot{-} \cdots \dot{-} \alpha_{k-1})
$$

for any $k < \omega$ and permutation $\sigma$ on $k$. By repeated uses of this fact, axiom (A2), and our supposition, we find that $\Gamma \vdash_Q ((1 \dot{-} 2^{-1}) \dot{-} 2^{-2}) \dot{-} \cdots \dot{-} 2^{-m}$, so $\Gamma$ is inconsistent, yielding a contradiction.

(ii) Suppose $\Gamma \cup \{\varphi \dot{-} \psi\}$ is inconsistent. Then by the Deduction Theorem, there is $n < \omega$ such that $\Gamma \vdash_Q 1 \dot{-} n(\varphi \dot{-} \psi)$. Observe that for all $m < \omega$, $\vdash^{\mathrm{L}} (\beta \dot{-} \alpha) \dot{-} (1 \dot{-} m(\alpha \dot{-} \beta))$, whereby it follows that $\vdash_Q (\varphi \dot{-} \psi) \dot{-} (1 \dot{-} n(\varphi \dot{-} \psi))$. Hence, by *modus ponens* we have $\Gamma \vdash_Q \psi \dot{-} \varphi$, so $\Gamma \cup \{\psi \dot{-} \varphi\}$ is consistent. $\square$

**Lemma 8.6.** Let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$ be consistent, and let $E(\Gamma) := \{\Gamma' : \Gamma \subseteq \Gamma' \subseteq \mathrm{For}(\mathcal{L}) \text{ and } \Gamma' \text{ is consistent}\}$. Then $\Delta$ is a maximal member of $E(\Gamma)$ if and only if for all formulae $\varphi$, $\psi$,

(i) $\Gamma \subseteq \Delta$ and $\Delta$ is consistent.

(ii) If $\Delta \vdash_Q \varphi \dot{-} 2^{-n}$ for all $n < \omega$ then $\varphi \in \Delta$.

(iii) $\varphi \dot{-} \psi \in \Delta$ or $\psi \dot{-} \varphi \in \Delta$.

*Proof.*

($\Rightarrow$) If $\Delta$ is a maximal member of $E(\Gamma)$, then (i) is immediate, while (ii) and (iii) follow from Lemma 8.5.

($\Leftarrow$) Suppose (i), (ii), and (iii) hold. Let $\Gamma' \in E(\Gamma)$ be such that $\Delta \subseteq \Gamma'$. Assume $\varphi \in \Gamma'$. Then for every $n < \omega$, $2^{-n} \dot{-} \varphi \notin \Gamma'$ and so $\varphi \dot{-} 2^{-n} \in \Delta$. It follows that $\varphi \in \Delta$, as desired. $\square$

**Remark 8.7.** In continuous propositional logic, conditions (ii) and (iii) are independent. To see this, let $\mathcal{S}$ be a continuous propositional logic. First we show that (ii) does not imply (iii). Let $\Delta := \{\varphi \in \mathcal{S} : \vdash^{\mathrm{CL}} \varphi\}$. Observe that by completeness of continuous

<!-- page 19 -->

propositional logic (Fact 4.5), $\Delta$ is consistent, and if $\Delta \vdash^{\mathrm{CL}} \varphi \dot{-} 2^{-n}$ for all $n < \omega$, then $\varphi \in \Delta$. However, since $\not\vdash^{\mathrm{CL}} P \dot{-} \frac{1}{2}$ and $\not\vdash^{\mathrm{CL}} \frac{1}{2} \dot{-} P$, neither $P \dot{-} \frac{1}{2}$ nor $\frac{1}{2} \dot{-} P$ is in $\Delta$. We now show that (iii) does not imply (ii). Let $\Gamma := \{P \dot{-} 2^{-n} : n < \omega\}$. Then $\Gamma$ is consistent, and so by (ii) of Lemma 8.5 we can construct a consistent set $\Delta \supseteq \Gamma$ such that for every $\varphi, \psi \in \mathcal{S}$, either $\varphi \dot{-} \psi \in \Delta$ or $\psi \dot{-} \varphi \in \Delta$. Nonetheless, $\Delta \vdash^{\mathrm{CL}} P \dot{-} 2^{-n}$ for all $n < \omega$, yet $P \notin \Delta$.

Lemma 8.6 justifies the following definition.

**Definition 8.8.** Let $\Delta \subseteq \mathrm{For}(\mathcal{L})$. We say that $\Delta$ is *maximal consistent* if $\Delta$ is consistent and for all formulae $\varphi$, $\psi$,

(i) If $\Delta \vdash_Q \varphi \dot{-} 2^{-n}$ for all $n < \omega$ then $\varphi \in \Delta$.

(ii) $\varphi \dot{-} \psi \in \Delta$ or $\psi \dot{-} \varphi \in \Delta$.

Condition (i) says that if $\Delta$ can furnish a series of proofs which altogether indicate that $\varphi$ is a consequence of $\Delta$, then $\Delta$ must be granted $\varphi$. Condition (ii) says that $\Delta$ can compare any two formulae.

*Remark 8.9.* Observe that if $\Delta$ is a maximal consistent set of formulae, then $\varphi \in \Delta$ if and only if $\Delta \vdash_Q \varphi$. It can be shown that in the above definition condition (i) can be replaced by condition $(i')$: If $\{\varphi \dot{-} 2^{-n} : n < \omega\} \subseteq \Delta$, then $\varphi \in \Delta$. Indeed, condition $(i')$ is also independent of (ii) in continuous propositional logic.

We thereby obtain the following result.

**Theorem 8.10.** *If $\Gamma \subseteq \mathrm{For}(\mathcal{L})$ is consistent, then there exists a maximal consistent set of formulae $\Delta \supseteq \Gamma$.*

*Proof.* By Zorn’s Lemma and Lemma 8.6. $\square$

**Lemma 8.11.** *Let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$, let $\Delta$ be a maximal consistent set of formulae containing $\Gamma$, let $t$ be a term, and let $p \in \mathbb{D}$. Then if $\sup_x \varphi \dot{-} p \in \Delta$, there is a formula $\varphi'$ such that $\varphi \equiv \varphi'$ and $\varphi'[t/x] \dot{-} p \in \Delta$.*

*Proof.* By Lemma 6.4 there is a formula $\varphi'$ such that no variable of $t$ is bound in $\varphi'$ and $\varphi \equiv \varphi'$, so by repeated applications of Lemma 8.3 and (A2), we have $\vdash_Q \varphi' \dot{-} \varphi$. Then by the Generalization Theorem, $\vdash_Q \sup_x (\varphi' \dot{-} \varphi)$, whence by (A7) it follows that $\vdash_Q \sup_x \varphi' \dot{-} \sup_x \varphi$. Now as $\sup_x \varphi \dot{-} p \in \Delta$, by (A2) we have $\Delta \vdash_Q \sup_x \varphi' \dot{-} p$. Because $\varphi'[t/x]$ is correct, again by (A2) and by (A8) we have $\Delta \vdash_Q \varphi'[t/x] \dot{-} \sup_x \varphi$, so once more by (A2) it follows that $\Delta \vdash_Q \varphi'[t/x] \dot{-} p$. Therefore, since $\Delta$ is maximal consistent, we conclude that $\varphi'[t/x] \dot{-} p \in \Delta$, as desired. $\square$

We will use the following lemma to define a continuous pre-structure and to help us in parts of our proof of completeness.

<!-- page 20 -->

**Lemma 8.12.** Let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$ be consistent, let $\Delta$ be a maximal consistent set of formulae containing $\Gamma$, and let $\varphi$ be a formula. Then

$$
\sup\{p \in \mathbb{D} : p \dot{-} \varphi \in \Delta\} = \inf\{q \in \mathbb{D} : \varphi \dot{-} q \in \Delta\}.
$$

*Proof.* Straightforward, by Lemma 8.6. $\square$

**9. COMPLETENESS THEOREM**

In classical first-order logic, we say that a set $\Gamma$ of formulae is *Henkin complete* if for every formula $\varphi$ and variable $x$, there is a constant $c$ such that

$$
\neg \forall x \varphi \to \neg \varphi[c/x] \in \Gamma.
$$

The intuition to define a Henkin complete set in continuous first-order logic as the syntactic translation of this definition will not work. Indeed, if $\Gamma$ is maximal consistent and $\neg \sup_x \neg \varphi \in \Gamma$, i.e., $\inf_x \varphi \in \Gamma$, we would be better off to not require that there is a constant $c$ such that $\varphi[c/x] \in \Gamma$. For example, a perfectly consistent situation could arise in which $\inf_x \varphi \in \Gamma$, there is a sequence of formulae $(\varphi[t_i/x] : i < \omega)$ such that $\Gamma \vdash_Q \varphi[t_n/x] \dot{-} 2^{-n}$ for each $n < \omega$, yet each term $t$ has a non-zero $p_t \in \mathbb{D}$ such that $\Gamma \vdash_Q p_t \dot{-} \varphi[t/x]$, whereby we should certainly not require that there is a term $t$ such that $\varphi[t/x] \in \Gamma$. Rather than attempt to prevent this sort of situation from ever occurring, we wish to accommodate this sort of situation in our definition of a Henkin complete set.

**Definition 9.1.** Let $\Gamma$ be a set of formulae. We say that $\Gamma$ is *Henkin complete* if for every formula $\varphi$, variable $x$, and $p, q \in \mathbb{D}$ with $p < q$, there is a constant symbol $c$ such that

$$
(\sup_x \varphi \dot{-} q) \wedge (p \dot{-} \varphi[c/x]) \in \Gamma.
$$

The next proposition guarantees we can construct a consistent Henkin complete set.

**Proposition 9.2.** Let $\mathcal{L}$ be a continuous signature. There exists a continuous signature $\mathcal{L}^c$ with $\mathcal{L} \subseteq \mathcal{L}^c$ and a set $\Gamma^c \subseteq \mathrm{For}(\mathcal{L}^c)$ such that for every $\Gamma \subseteq \mathrm{For}(\mathcal{L})$,

(i) $\Gamma \cup \Gamma^c$ is Henkin complete.

(ii) If $\Gamma$ is consistent, then $\Gamma \cup \Gamma^c$ is consistent.

*Proof.* Permitting some abuse of notation, we define an increasing sequence of signatures inductively:

$$
\mathcal{L}_0 := \mathcal{L}
$$

$$
\mathcal{L}_{n+1} := \mathcal{L}_n \cup \{c_{(\varphi,x,p,q)} : \varphi \in \mathrm{For}(\mathcal{L}_n), x \in V, \text{ and } p, q \in \mathbb{D} \text{ with } p < q\}
$$

where each $c_{(\varphi,x,p,q)}$ is a new constant symbol. We then put

$$
\mathcal{L}^c := \bigcup_{n < \omega} \mathcal{L}_n
$$

$$
\psi_{(\varphi,x,p,q)} := (\sup_x \varphi \dot{-} q) \wedge (p \dot{-} \varphi[c_{(\varphi,x,p,q)}/x]) \quad\text{and}
$$

$$
\Gamma^c := \{\psi_{(\varphi,x,p,q)} : \varphi \in \mathrm{For}(\mathcal{L}^c), x \in V, \text{ and } p, q \in \mathbb{D} \text{ with } p < q\}.
$$

<!-- page 21 -->

(i) is obviously true, so we proceed to establish (ii).

Suppose $\Gamma$ is consistent. For *reductio ad absurdum*, assume $\Gamma \cup \Gamma^c$ is inconsistent. Then there is a minimal finite non-empty $\Gamma^c_0 \subseteq \Gamma^c$ such that $\Gamma \cup \Gamma^c_0$ is inconsistent. We may write $\Gamma^c_0 = \{\psi_{(\varphi_i,x_i,p_i,q_i)} : i < n\}$, where the $(\varphi_i, x_i, p_i, q_i)$ are pairwise distinct. For each $i < n$, there is a minimal $m_i$ such that $\varphi_i \in \mathrm{For}(\mathcal{L}_{m_i})$. Let $m_{i_0}$ be the maximal such $m_i$. For simplicity of notation, put $\varphi := \varphi_{i_0}$, $x := x_{i_0}$, $p := p_{i_0}$, $q := q_{i_0}$, and $m := m_{i_0}$.

Now observe that for each $i < n$, $\varphi_i \in \mathrm{For}(\mathcal{L}_m)$, while $c_{(\varphi,x,p,q)} \in \mathcal{L}_{m+1} \setminus \mathcal{L}_m$. Put $\Gamma^c_1 := \Gamma^c_0 \setminus \{\psi_{(\varphi,x,p,q)}\}$ and $\Gamma_1 := \Gamma \cup \Gamma^c_1$. Note that $c_{(\varphi,x,p,q)}$ does not occur in $\Gamma_1$ and that $\Gamma_1$ must be consistent (by the minimality of $\Gamma^c_0$). Nonetheless, $\Gamma \cup \Gamma^c_0 = \Gamma_1 \cup \{(\sup_x \varphi \dot{-} q) \wedge (p \dot{-} \varphi[c_{(\varphi,x,p,q)}/x])\}$ is inconsistent. Observe that $\vdash^{\mathrm{L}} (\alpha \wedge \beta) \dot{-} \alpha$ and $\vdash^{\mathrm{L}} (\alpha \wedge \beta) \dot{-} \beta$. Thus, by *modus ponens*,

$$
\begin{aligned}
\Gamma_1 \cup \{(\sup_x \varphi \dot{-} q)\} &\vdash_Q (\sup_x \varphi \dot{-} q) \wedge (p \dot{-} \varphi[c_{(\varphi,x,p,q)}/x]), \quad \text{and} \\
\Gamma_1 \cup \{(p \dot{-} \varphi[c_{(\varphi,x,p,q)}/x])\} &\vdash_Q (\sup_x \varphi \dot{-} q) \wedge (p \dot{-} \varphi[c_{(\varphi,x,p,q)}/x]).
\end{aligned}
$$

Since $\Gamma \cup \Gamma^c_0$ is inconsistent, by the Deduction Theorem there is $n < \omega$ such that

$$
\Gamma_1 \vdash_Q 1 \dot{-} n\bigl((\sup_x \varphi \dot{-} q) \wedge (p \dot{-} \varphi[c_{(\varphi,x,p,q)}/x])\bigr).
$$

Therefore, by *modus ponens*, we find that $\Gamma_1 \cup \{(\sup_x \varphi \dot{-} q)\}$ and $\Gamma_1 \cup \{(p \dot{-} \varphi[c_{(\varphi,x,p,q)}/x])\}$ are both inconsistent. It follows that $\Gamma_1 \vdash_Q (q \dot{-} \sup_x \varphi)$ and $\Gamma_1 \vdash_Q (\varphi[c_{(\varphi,x,p,q)}/x] \dot{-} p)$ (cf. proof of Lemma 8.5).

Now let $y$ be a variable not occurring in $\varphi$. On the one hand, by Lemma 8.3 we have $\vdash_Q (q \dot{-} \sup_x \varphi)\{y/x\} \dot{-} (q \dot{-} \sup_x \varphi)$, so by *modus ponens*,

$$
\begin{aligned}
\Gamma_1 \vdash_Q (q \dot{-} \sup_x \varphi)\{y/x\} &= (q\{y/x\} \dot{-} \sup_y \varphi[y/x]) \\
&= (q \dot{-} \sup_y \varphi[y/x]).
\end{aligned}
$$

On the other hand, because $c_{(\varphi,x,p,q)}$ does not occur in $\Gamma_1$, by Lemma 8.4 we have

$$
\begin{aligned}
\Gamma_1 \vdash_Q \sup_y(\varphi[c_{(\varphi,x,p,q)}/x] \dot{-} p)[y/c_{(\varphi,x,p,q)}] &= \sup_y(\varphi[c_{(\varphi,x,p,q)}/x][y/c_{(\varphi,x,p,q)}] \dot{-} p[y/c_{(\varphi,x,p,q)}]) \\
&= \sup_y (\varphi[y/x] \dot{-} p).
\end{aligned}
$$

Then by (A7) and *modus ponens*, $\Gamma_1 \vdash_Q \sup_y \varphi[y/x] \dot{-} \sup_y p$. Since $y$ is not free in $p$, (A9) yields $\Gamma_1 \vdash_Q \sup_y p \dot{-} \sup_y \varphi$. Thus by (A2) and *modus ponens*, $\Gamma_1 \vdash_Q \sup_y \varphi[y/x] \dot{-} p$.

It remains to observe that since $\Gamma_1 \vdash_Q (q \dot{-} \sup_y \varphi[y/x])$ and $\Gamma_1 \vdash_Q \sup_y \varphi[y/x] \dot{-} p$, by (A2) we have $\Gamma_1 \vdash_Q q \dot{-} p$, so $\Gamma$ is inconsistent, which is impossible ($q \dot{-} p \in \mathbb{D}$ and $q \dot{-} p > 0$ by construction). $\square$

**Definition 9.3.** We define the *rank* of $\varphi$, $rank(\varphi)$, by recursion:

$$
\begin{aligned}
rank(P t_0 \cdots t_{n_P-1}) &:= 0, \\
rank(\tfrac{1}{2}\varphi) &:= rank(\varphi) + 1, \\
rank(\neg\varphi) &:= rank(\varphi) + 1, \\
rank(\varphi \dot{-} \psi) &:= rank(\varphi) + rank(\psi) + 1, \\
rank(\sup_x \varphi) &:= rank(\varphi) + 1.
\end{aligned}
$$

**Theorem 9.4.** Let $\mathcal{L}$ be a continuous signature (possibly with a metric), and let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$. Assume $\Gamma$ is consistent. Then there is a continuous signature $\mathcal{L}^c \supseteq \mathcal{L}$, a maximal

<!-- page 22 -->

consistent and Henkin complete set $\Delta \subseteq \mathrm{For}(\mathcal{L}^c)$ with $\Delta \supseteq \Gamma$, a continuous $\mathcal{L}^c$-prestructure $\mathfrak{M}$, and an $\mathfrak{M}$-assignment $\sigma$ such that $(\mathfrak{M}, \sigma) \vDash_Q \Delta$.

*Proof.* Suppose $\Gamma$ is consistent. By the previous proposition, there is $\Gamma^c \subseteq \mathrm{For}(\mathcal{L}^c)$ such that $\Gamma \cup \Gamma^c$ is consistent and Henkin complete, so by Theorem 8.10 there is a maximal consistent $\Delta \subseteq \mathrm{For}(\mathcal{L}^c)$ such that $\Delta \supseteq \Gamma \cup \Gamma^c$. Define a continuous $\mathcal{L}^c$-prestructure $\mathfrak{M}$ such that $M$ is the set of all $\mathcal{L}^c$-terms.

(i) For each $f \in \mathcal{F}$, define $f^{\mathfrak{M}} : M^{n_f} \to M$ by setting $f^{\mathfrak{M}}(t_0, \ldots, t_{n_f-1}) := f t_0 \cdots t_{n_f-1}$ for all $t_0, \ldots, t_{n_f-1} \in M$.

(ii) For each $P \in \mathcal{R}$, define $P^{\mathfrak{M}} : M^{n_P} \to [0, 1]$ by setting $P^{\mathfrak{M}}(t_0, \ldots, t_{n_P-1}) := \sup\{p \in \mathbb{D} : p \dot{-} P t_0 \cdots t_{n_P-1} \in \Delta\}$ for all $t_0, \ldots, t_{n_P-1} \in M$.

Define an $\mathfrak{M}$-assignment $\sigma$ by setting $\sigma(x) := x$ for all $x \in V$. It is a simple matter to check that $t^{\mathfrak{M}, \sigma} = t$ for all terms $t$.

It suffices to prove by induction on the number of quantifiers and connectives in $\varphi$, i.e., the rank of $\varphi$, that $\mathfrak{M}(\varphi, \sigma) = \sup\{p \in \mathbb{D} : p \dot{-} \varphi \in \Delta\}$ for all $\varphi \in \mathrm{For}(\mathcal{L}^c)$. For the sake of brevity, here we only consider the subcases $\varphi = \frac{1}{2}\psi$ and $\varphi = \sup_x \psi$. Although the case for $\mathrm{rank}(\varphi) = 0$ is trivial, we encourage the reader to work out the subcases of $\neg$ and $\dot{-}$ for $\mathrm{rank}(\varphi) > 0$.

$\varphi = \frac{1}{2}\psi$: We wish to show that $\mathfrak{M}(\frac{1}{2}\psi, \sigma) = \sup\{p \in \mathbb{D} : p \dot{-} \frac{1}{2}\psi \in \Delta\}$. By definition, $\mathfrak{M}(\frac{1}{2}\psi, \sigma) = \frac{1}{2}\sup\{p \in \mathbb{D} : p \dot{-} \psi \in \Delta\}$, and by induction hypothesis, $\mathfrak{M}(\psi, \sigma) = \sup\{p \in \mathbb{D} : p \dot{-} \psi \in \Delta\}$. We must therefore show $\frac{1}{2}\sup\{p \in \mathbb{D} : p \dot{-} \psi \in \Delta\} = \sup\{p \in \mathbb{D} : p \dot{-} \frac{1}{2}\psi \in \Delta\}$. We consider two cases.

(a) By Fact 4.5, since $\Delta$ is maximal consistent, for every $p \in \mathbb{D}$, $p \dot{-} \frac{1}{2}\psi \in \Delta$ only if $\neg(\neg p \dot{-} p) \dot{-} \psi \in \Delta$. Hence, for every $p \in \mathbb{D}$ such that $p \dot{-} \frac{1}{2}\psi \in \Delta$, $p \le \frac{1}{2}\neg(\neg p \dot{-} p) \le \frac{1}{2}\sup\{p \in \mathbb{D} : p \dot{-} \psi \in \Delta\}$. It follows that $\sup\{p \in \mathbb{D} : p \dot{-} \frac{1}{2}\psi \in \Delta\} \le \frac{1}{2}\sup\{p \in \mathbb{D} : p \dot{-} \psi \in \Delta\}$.

(b) By Fact 4.5, since $\Delta$ is maximal consistent, for every $p \in \mathbb{D}$, $p \dot{-} \psi \in \Delta$ only if $\frac{1}{2}p \dot{-} \frac{1}{2}\psi \in \Delta$ (cf. proof of Lemma 8.3). Hence, for every $p \in \mathbb{D}$ such that $p \dot{-} \psi \in \Delta$, $\frac{1}{2}p \le \sup\{p \in \mathbb{D} : p \dot{-} \frac{1}{2}\psi \in \Delta\}$ and therefore $p \le 2\sup\{p \in \mathbb{D} : p \dot{-} \frac{1}{2}\psi \in \Delta\}$. It follows that $\sup\{p \in \mathbb{D} : p \dot{-} \psi \in \Delta\} \le 2\sup\{p \in \mathbb{D} : p \dot{-} \frac{1}{2}\psi \in \Delta\}$, whence $\frac{1}{2}\sup\{p \in \mathbb{D} : p \dot{-} \psi \in \Delta\} \le \sup\{p \in \mathbb{D} : p \dot{-} \frac{1}{2}\psi \in \Delta\}$, as desired.

$\varphi = \sup_x \psi$: We wish to show that $\mathfrak{M}(\sup_x \psi, \sigma) = \sup\{p \in \mathbb{D} : p \dot{-} \sup_x \psi \in \Delta\}$. Observe that by definition $\mathfrak{M}(\sup_x \psi, \sigma) = \sup\{\mathfrak{M}(\psi, \sigma_x^t) : t \in M\}$. So it suffices to show that $\sup\{\mathfrak{M}(\psi, \sigma_x^t) : t \in M\} = \sup\{p \in \mathbb{D} : p \dot{-} \sup_x \psi \in \Delta\}$. For *reductio ad absurdum*, assume this equality fails to hold. We of course consider two cases.

(a) Suppose $\sup\{\mathfrak{M}(\psi, \sigma_x^t) : t \in M\} < \sup\{p \in \mathbb{D} : p \dot{-} \sup_x \psi \in \Delta\}$. Then for some $p, q \in \mathbb{D}$, $\sup\{\mathfrak{M}(\psi, \sigma_x^t) : t \in M\} < p < q < \sup\{p \in \mathbb{D} : p \dot{-} \sup_x \psi \in \Delta\}$. Since $\Gamma^c \subseteq \Delta$ and $p < q$, there is a constant $c$ such that $(\sup_x \psi \dot{-} q) \wedge (p \dot{-} \psi[c/x]) \in$

<!-- page 23 -->

$\Delta$. Furthermore, there is $r \in \mathbb{D}$ such that $q < r$ and $r \dot{-} \sup_x \psi \in \Delta$. As $\Delta$ is maximal consistent, by Fact 4.5 it follows that $p \dot{-} \psi[c/x] \in \Delta$. Since $rank(\psi[c/x]) < rank(\varphi)$, our induction hypothesis tells us that $\mathfrak{M}(\psi[c/x], \sigma) = \sup\{p \in \mathbb{D} : p \dot{-} \psi[c/x] \in \Delta\}$. Also, since $\psi[c/x]$ is correct, by Lemma 6.2 it follows that $\mathfrak{M}(\psi[c/x], \sigma) = \mathfrak{M}(\psi, \sigma_x^c)$. Thus $p \le \mathfrak{M}(\psi, \sigma_x^c) \le \sup\{\mathfrak{M}(\psi, \sigma_x^t) : t \in M\}$, yielding a contradiction.

(b) Suppose $\sup\{p \in \mathbb{D} : p \dot{-} \sup_x \psi \in \Delta\} < \sup\{\mathfrak{M}(\psi, \sigma_x^t) : t \in M\}$. On the one hand, since $\Delta$ is maximal consistent, for all $p \in \mathbb{D}$ such that $p > \sup\{p \in \mathbb{D} : p \dot{-} \sup_x \psi \in \Delta\}$, $\sup_x \psi \dot{-} p \in \Delta$. On the other hand, there must be $t \in M$ such that $\mathfrak{M}(\psi, \sigma_x^t) > \sup\{p \in \mathbb{D} : p \dot{-} \sup_x \psi \in \Delta\}$, so there is $p \in \mathbb{D}$ such that $\mathfrak{M}(\psi, \sigma_x^t) > p > \sup\{p \in \mathbb{D} : p \dot{-} \sup_x \psi \in \Delta\}$. Thus $\sup_x \psi \dot{-} p \in \Delta$, whence by Lemma 8.11, there is $\psi' \equiv \psi$ such that $\psi'[t/x] \dot{-} p \in \Delta$. Thus $\inf\{p : \psi'[t/x] \dot{-} p \in \Delta\} \le p$. By Lemma 8.12, $\inf\{p : \psi'[t/x] \dot{-} p \in \Delta\} = \sup\{p \in \mathbb{D} : p \dot{-} \psi'[t/x] \in \Delta\}$, and because $rank(\psi'[t/x]) < rank(\varphi)$, our induction hypothesis tells us that $\mathfrak{M}(\psi'[t/x], \sigma) = \sup\{p \in \mathbb{D} : p \dot{-} \psi'[t/x] \in \Delta\}$. Moreover, since $\psi'[t/x]$ is correct, $\mathfrak{M}(\psi'[t/x], \sigma) = \mathfrak{M}(\psi', \sigma_x^t)$ by Lemma 6.2. Finally, since $\psi' \equiv \psi$, we have $\mathfrak{M}(\psi', \sigma_x^t) = \mathfrak{M}(\psi, \sigma_x^t)$. It follows that $\mathfrak{M}(\psi, \sigma_x^t) \le p$, yielding another contradiction.

Now if $\varphi \in \Delta$, then by (A1), $\varphi \dot{-} 0 \in \Delta$, so $\mathfrak{M}(\varphi, \sigma) = \sup\{p \in \mathbb{D} : p \dot{-} \varphi \in \Delta\} = \inf\{q \in \mathbb{D} : \varphi \dot{-} q \in \Delta\} = 0$ (Lemma 8.12). This shows that $(\mathfrak{M}, \sigma) \vDash_Q \Delta$, proving our theorem. $\square$

We may now state and prove the long-awaited completeness theorem.

**Theorem 9.5 (Completeness for Continuous First-Order Logic).** *Let $\mathcal{L}$ be a continuous signature, and let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$. Then $\Gamma$ is consistent only if $\Gamma$ is satisfiable. Furthermore, if $\mathcal{L}$ is a continuous signature with a metric, then $\Gamma$ is consistent only if $\Gamma$ is completely satisfiable.*

*Proof.* By Theorem 9.4, there is a continuous signature $\mathcal{L}^c \supseteq \mathcal{L}$, a maximal consistent set $\Delta \subseteq \mathrm{For}(\mathcal{L}^c)$ with $\Delta \supseteq \Gamma$, an $\mathcal{L}^c$-pre-structure $\mathfrak{M}$, and an $\mathfrak{M}$-assignment $\sigma$ such that $(\mathfrak{M}, \sigma) \vDash_Q \Delta$. If $\mathcal{L}$ does not have a metric, we are done; we observe $(\mathfrak{M}, \sigma)$ models $\Gamma$ and simply restrict $\mathfrak{M}$ to our original signature. But if $\mathcal{L}$ has a metric $d$, we can only guarantee that $d^{\mathfrak{M}}$ is a pseudo-metric relative to this restriction. We wish to find a continuous $\mathcal{L}$-structure $\widehat{\mathfrak{M}}$ and an $\widehat{\mathfrak{M}}$-assignment $\widehat{\sigma}$ such that $(\widehat{\mathfrak{M}}, \widehat{\sigma}) \vDash_Q \Gamma$. By Theorem 6.9, there is a continuous $\mathcal{L}$-structure $\widehat{\mathfrak{M}}$ and an $\mathcal{L}$-morphism $h : M \to \widehat{M}$ such that for every formula $\varphi$, $\mathfrak{M}(\varphi, \sigma) = \widehat{\mathfrak{M}}(\varphi, h \circ \sigma)$. Therefore, putting $\widehat{\sigma} := h \circ \sigma$, since $(\mathfrak{M}, \sigma)$ models $\Gamma$, $(\widehat{\mathfrak{M}}, \widehat{\sigma})$ models $\Gamma$. $\square$

We conclude with several corollaries. The following result has a counterpart in [Hay63] (see also [Háj98]).

<!-- page 24 -->

ITAÏ BEN YAACOV AND ARTHUR PAUL PEDERSEN

**Corollary 9.6 (Approximated Strong Completeness for Continuous Logic).** *Let $\mathcal{L}$ be a continuous signature, let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$, and let $\varphi$ be a formula. Then $\Gamma \vDash_Q \varphi$ if and only if $\Gamma \vdash_Q \varphi \dot{-} 2^{-n}$ for all $n < \omega$. Moreover, if $\mathcal{L}$ is a continuous signature with a metric, then $\Gamma \vDash_{QC} \varphi$ if and only if $\Gamma \vdash_Q \varphi \dot{-} 2^{-n}$ for all $n < \omega$.*

*Proof.* Right to left is by soundness (Theorem 7.2). For the implication from left to right, if $\Gamma \vDash \varphi$, then for every $n < \omega$, $\Gamma \cup \{2^{-n} \dot{-} \varphi\}$ is not (completely) satisfiable and so inconsistent by Theorem 9.5; hence, $\Gamma \vdash \varphi \dot{-} 2^{-n}$ for all $n < \omega$ (cf. proof of Lemma 8.5). $\square$

We can, however, try to make the best of the previous result. We first offer a definition.

**Definition 9.7.** Let $\mathcal{L}$ be a continuous signature (possibly with a metric), let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$, and let $\varphi$ be a formula.

(i) We define the *degree of truth* of $\varphi$ with respect to $\Gamma$, $\varphi^{\circ}_{\Gamma}$, by setting
$$\varphi^{\circ}_{\Gamma} := \sup\{\mathfrak{M}(\varphi, \sigma) : (\mathfrak{M}, \sigma) \vDash \Gamma\}.$$

(ii) We define the *degree of provability* of $\varphi$ with respect to $\Gamma$, $\varphi^{\circledcirc}_{\Gamma}$, by setting
$$\varphi^{\circledcirc}_{\Gamma} := \inf\{p \in \mathbb{D} : \Gamma \vdash \varphi \dot{-} p\}.$$

We then have the following result, commonly called *Pavelka-style completeness*.

**Corollary 9.8.** *Let $\mathcal{L}$ be a continuous signature, and let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$. Then for every formula $\varphi$, the degree of truth of $\varphi$ with respect to $\Gamma$ equals the degree of provability of $\varphi$ with respect to $\Gamma$. In other words,*
$$\varphi^{\circ}_{\Gamma} = \varphi^{\circledcirc}_{\Gamma}.$$

*Proof.* We consider two cases:

(i) We first show $\varphi^{\circ}_{\Gamma} \le \varphi^{\circledcirc}_{\Gamma}$. This follows from soundness (Theorem 7.2). To see this, observe that for every $p \in \mathbb{D}$ such that $\Gamma \vdash \varphi \dot{-} p$, by soundness $\Gamma \vDash \varphi \dot{-} p$, so for any continuous $\mathcal{L}$(-pre)-structure $\mathfrak{M}$ and $\mathfrak{M}$-assignment $\sigma$ such that $(\mathfrak{M}, \sigma) \vDash \Gamma$, $\mathfrak{M}(\varphi, \sigma) \le p$; thus, $\varphi^{\circ}_{\Gamma} \le p$. It follows that $\varphi^{\circ}_{\Gamma} \le \varphi^{\circledcirc}_{\Gamma}$.

(ii) We now show $\varphi^{\circ}_{\Gamma} \ge \varphi^{\circledcirc}_{\Gamma}$. It suffices to show that for each $p \in \mathbb{D}$ such that $p < \varphi^{\circledcirc}_{\Gamma}$, there is a continuous $\mathcal{L}$(-pre)-structure $\mathfrak{M}$ and $\mathfrak{M}$-assignment $\sigma$ such that $(\mathfrak{M}, \sigma) \vDash \Gamma$ and $p \le \mathfrak{M}(\varphi, \sigma)$. Let $p \in \mathbb{D}$, and suppose $p < \varphi^{\circledcirc}_{\Gamma}$. Then $\Gamma \nvdash \varphi \dot{-} p$, so $\Gamma \cup \{p \dot{-} \varphi\}$ is consistent (cf. proof of Lemma 8.5), whence by Theorem 9.5, $\Gamma \cup \{p \dot{-} \varphi\}$ is (completely) satisfiable. Hence, there is a continuous $\mathcal{L}$(-pre)-structure $\mathfrak{M}$ and $\mathfrak{M}$-assignment $\sigma$ such that $(\mathfrak{M}, \sigma) \vDash \Gamma$ and $\mathfrak{M}(p \dot{-} \varphi, \sigma) = 0$, so $p \le \mathfrak{M}(\varphi, \sigma)$. $\square$

**Definition 9.9.** Let $\mathcal{L}$ be a continuous signature with a metric.

(i) We call $T$ a *theory* if $T$ is a set of formulae in $\mathcal{L}$ without free variables, i.e., a set of sentences.

<!-- page 25 -->

**A PROOF OF COMPLETENESS**

(ii) We call a theory $T$ *complete* if there is a continuous $\mathcal{L}$-structure $\mathfrak{M}$ (and an $\mathfrak{M}$-assignment $\sigma$) such that $T = \{\varphi : (\mathfrak{M}, \sigma) \vDash_{QC} \varphi\}$. Otherwise, we call $T$ an *incomplete theory*.

**Definition 9.10.** Let $T$ be a theory.

(i) If $T$ is complete, we say $T$ is *decidable* if for every sentence $\varphi$, the value $\varphi^{\circ}_T$ is a recursive real and uniformly computable from $\varphi$.

(ii) If $T$ is incomplete, we say $T$ is *decidable* if for every sentence $\varphi$ the real number $\varphi^{\circ}_T$ is uniformly recursive from $\varphi$.

**Corollary 9.11.** *Every complete theory with a recursive or recursively enumerable axiomatization is decidable.*

As with classical first-order logic, the following corollary could be obtained more directly by way of an ultraproduct construction (see [BU]). We nevertheless include it for the sake of completeness.

**Corollary 9.12 (Compactness).** *Let $\mathcal{L}$ be a continuous signature, and let $\Gamma \subseteq \mathrm{For}(\mathcal{L})$. If every finite subset $\Gamma_0$ of $\Gamma$ is (completely) satisfiable, then $\Gamma$ is (completely) satisfiable.*

**REFERENCES**

[BBHU08] Itaï Ben Yaacov, Alexander Berenstein, C. Ward Henson, and Alexander Usvyatsov, *Model theory for metric structures*, Model theory with Applications to Algebra and Analysis, volume 2 (Zoé Chatzidakis, Dugald Macpherson, Anand Pillay, and Alex Wilkie, eds.), London Math Society Lecture Note Series, vol. 350, 2008, pp. 315–427.

[BC63] L.P. Belluce and C.C. Chang, *A weak completeness theorem for infinite valued first-order logic*, Journal of Symbolic logic **28** (1963), no. 1, 43–50.

[Ben] Itaï Ben Yaacov, *On theories of random variables*, in preparation.

[Ben03a] ______, *Positive model theory and compact abstract theories*, Journal of Mathematical Logic **3** (2003), no. 1, 85–118.

[Ben03b] ______, *Simplicity in compact abstract theories*, Journal of Mathematical Logic **3** (2003), no. 2, 163–191.

[Ben05] ______, *Uncountable dense categoricity in cats*, Journal of Symbolic Logic **70** (2005), no. 3, 829–860.

[BU] Itaï Ben Yaacov and Alexander Usvyatsov, *Continuous first order logic and local stability*, Transactions of the American Mathematical Society, to appear.

[CDM00] Roberto L.O. Cignoli, Itala M.L. D'Ottaviano, and Daniele Mundici, *Algebraic foundations of many-valued reasoning*, Trends in Logic—Studia Logica Library, vol. 7, Kluwer Academic Publishers, Dordrecht, 2000.

[Cha58] C. C. Chang, *Proof of an axiom of Łukasiewicz*, Transactions of the American Mathematical Society **87** (1958), 55–56.

[Cha59] ______, *A new proof of the completeness of the Łukasiewicz axioms*, Transactions of the American Mathematical Society **93** (1959), 74–80.

[CK66] C. C. Chang and H. Jerome Keisler, *Continuous model theory*, Princeton University Press, 1966.

<!-- page 26 -->

ITAÏ BEN YAACOV AND ARTHUR PAUL PEDERSEN

**[EFT94]** H.-D. Ebbinghaus, J. Flum, and W. Thomas, *Mathematical logic*, second ed., Undergraduate Texts in Mathematics, Springer-Verlag, New York, 1994, Translated from the German by Margit Meßmer.

**[End01]** Herbert B. Enderton, *A mathematical introduction to logic*, second ed., Harcourt/Academic Press, Burlington, MA, 2001.

**[Háj98]** Petr Hájek, *Metamathematics of fuzzy logic*, Trends in Logic—Studia Logica Library, vol. 4, Kluwer Academic Publishers, Dordrecht, 1998.

**[Hay63]** Louise Schmir Hay, *Axiomatization of the infinite-valued predicate calculus*, Journal of Symbolic Logic **28** (1963), no. 1, 77–86.

**[Hen76]** C. Ward Henson, *Nonstandard hulls of Banach spaces*, Israel Journal of Mathematics **25** (1976), 108–144.

**[Pav79]** Jan Pavelka, *On fuzzy logic I, II and III*, Zeitschrift für Mathematische Logik und Grundlagen der Mathematik **25** (1979), no. 5, 45–52, 119–134, 447–464.

**[RR58]** Alan Rose and J. Barkley Rosser, *Fragments of many-valued statement calculi*, Transactions of the American Mathematical Society **87** (1958), 1–53.

Itaï Ben Yaacov, Université Claude Bernard – Lyon 1, Institut Camille Jordan, 43 boulevard du 11 novembre 1918, 69622 Villeurbanne Cedex, France

URL: http://math.univ-lyon1.fr/~begnac

Arthur Paul Pedersen, Department of Philosophy, Carnegie Mellon University, Pittsburgh, PA 15213, USA

E-mail address: apaulpedersen@cmu.edu

URL: http://andrew.cmu.edu/~ppederse
