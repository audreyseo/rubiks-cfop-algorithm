# The Daisy Algorithm

We describe and prove correct an algorithm that, given an arbitrary state of a Rubik's cube, produces a sequence of face turns whose application places the four white edge pieces around the yellow center, forming a "daisy" pattern on top.

Throughout, the top face has white centers, the bottom face has yellow, and the four side faces are labelled F (front), R (right), B (back), L (left). We write U, D, F, R, B, L both for the faces and for the corresponding clockwise quarter-turn moves; together with their inverses these eighteen face turns generate the cube group $G$.

## §1. Setting

An *edge sticker* is an ordered pair $(a, b)$ of distinct adjacent faces, viewed as the sticker showing on face $a$ of the edge between $a$ and $b$. There are $24$ edge stickers, partitioned into $12$ unordered pairs (one per edge). For an edge sticker $s = (a, b)$ we write $s^* = (b, a)$ for its *flip*; $s^{**} = s$.

A *state* of the cube records the current position of each sticker; equivalently, it determines a permutation $\pi_c$ of the $24$ edge stickers. (Corner stickers behave analogously and play no role in this chapter.) Edge structure is preserved: any cube motion carries the pair $\{s, s^*\}$ to another such pair, so

$$\pi_c(s^*) = \pi_c(s)^* \qquad \text{(edge-flip identity).} \tag{1.1}$$

We adopt the **passive convention**: $\pi_c(s)$ is the *original* label of the sticker now at position $s$ in state $c$. Composition is written left-to-right: $\pi_{c_1 c_2} = \pi_{c_1} \circ \pi_{c_2}$, where $(f \circ g)(s) = f(g(s))$.

A sticker at position $s$ in state $c$ is **white** if and only if the first coordinate of $\pi_c(s)$ is U. We denote this predicate $W(c, s)$. Equivalently, the white edges are those originally labelled $(U, F), (U, R), (U, B), (U, L)$.

A *move sequence* is a finite word $m = r_1 \cdots r_n$ in the face symbols. We identify $m$ with its product as a cube transformation, and write $c \cdot m$ for the result of applying $m$ after $c$.

## §2. The y-rotation symmetry

The cube has a four-fold symmetry axis through the U and D centers. Conjugation by a quarter-turn about this axis permutes the four side faces in the cycle $F \to R \to B \to L \to F$, and fixes U and D. We exploit this symmetry to derive the four slot algorithms of §3 from a single base case.

**Definition 2.1.** Let $\sigma$ be the permutation of $\{U, D, F, R, B, L\}$ fixing U and D and cycling $F \to R \to B \to L \to F$.

**Definition 2.2.** For an edge sticker $s = (a, b)$, set $\rho(s) := (\sigma a, \sigma b)$. Adjacency is preserved by $\sigma$, so $\rho$ is a well-defined permutation of the $24$ edge stickers.

**Definition 2.3.** For a move sequence $m = r_1 \cdots r_n$, let $\sigma(m) := (\sigma r_1) \cdots (\sigma r_n)$.

**Theorem 2.4 (single-turn conjugacy).** *For every face turn $r$,*
$$\pi_{\sigma(r)} = \rho \circ \pi_r \circ \rho^{-1}. \tag{2.1}$$

The identity is verified by inspecting the action on each of the $24$ edge stickers, for each of the six face symbols.

**Theorem 2.5 (symmetry meta-lemma).** *For every move sequence $m$,*
$$\pi_{\sigma(m)} = \rho \circ \pi_m \circ \rho^{-1}. \tag{2.2}$$

*Proof.* By induction on the length of $m$. The empty case is trivial. For $m = r \cdot m'$, multiplicativity of $\pi$ and the inductive hypothesis give
$$\pi_{\sigma(m)} = \pi_{\sigma(r)} \circ \pi_{\sigma(m')} = (\rho \circ \pi_r \circ \rho^{-1}) \circ (\rho \circ \pi_{m'} \circ \rho^{-1}) = \rho \circ \pi_r \circ \pi_{m'} \circ \rho^{-1} = \rho \circ \pi_m \circ \rho^{-1}. \qquad \blacksquare$$

**Corollary 2.6.** *For every $k \geq 0$ and every move sequence $m$, $\pi_{\sigma^k(m)} = \rho^k \circ \pi_m \circ \rho^{-k}$.*

## §3. Slots, cases, and the F-base algorithm

A *slot* is one of the four U-edge target positions $\mathrm{UF}, \mathrm{UR}, \mathrm{UB}, \mathrm{UL}$. We index them by
$$i(\mathrm{UF}) = 0, \quad i(\mathrm{UR}) = 1, \quad i(\mathrm{UB}) = 2, \quad i(\mathrm{UL}) = 3.$$

A *case tag* is one of five symbols $F2, F6, R4, F8, D2$, naming the five sticker positions that the F-face base algorithm can lift into the UF target. The base data, copied verbatim from the standard daisy procedure, are:

| $t$ | source $S_0(t)$ | moves $M_0(t)$ |
|-----|----------------------|----------------|
| F2  | $(F, U)$             | $F\, U'\, R\, U$ |
| F6  | $(F, R)$             | $U'\, R\, U$     |
| R4  | $(R, F)$             | $F'$              |
| F8  | $(F, D)$             | $F'\, U'\, R\, U$ |
| D2  | $(D, F)$             | $F^2$             |

with target $T_0 := (U, F)$.

**Definition 3.1.** For each slot $s$ and case tag $t$,
$$T(s) := \rho^{i(s)}(T_0), \qquad S(s, t) := \rho^{i(s)}(S_0(t)), \qquad M(s, t) := \sigma^{i(s)}(M_0(t)).$$

The four targets evaluate to $T(\mathrm{UF}) = (U, F)$, $T(\mathrm{UR}) = (U, R)$, $T(\mathrm{UB}) = (U, B)$, $T(\mathrm{UL}) = (U, L)$. Each move sequence $M(s, t)$ is the face-relabeled image of $M_0(t)$ under $F \to R \to B \to L \to F$.

## §4. Per-case correctness

**Theorem 4.1 (base case).** *For every case tag $t$, $\pi_{M_0(t)}(T_0) = S_0(t)$.*

The five identities are verified by direct symbolic evaluation; e.g. for $t = F2$, applying $F\, U'\, R\, U$ to the solved cube sends the $(F, U)$ sticker to $(U, F)$.

**Theorem 4.2 (target lemma).** *For every slot $s$ and case tag $t$,*
$$\pi_{M(s, t)}(T(s)) = S(s, t). \tag{4.1}$$

*Proof.* Set $k := i(s)$ and write $P := \pi_{M_0(t)}$. By Corollary 2.6,
$$\pi_{M(s, t)} = \pi_{\sigma^k(M_0(t))} = \rho^k \circ P \circ \rho^{-k}.$$
Applying both sides to $T(s) = \rho^k(T_0)$:
$$\pi_{M(s, t)}(T(s)) = (\rho^k \circ P \circ \rho^{-k})(\rho^k(T_0)) = \rho^k(P(T_0)) = \rho^k(S_0(t)) = S(s, t),$$
using Theorem 4.1 and Definition 3.1 in the last two equalities. $\blacksquare$

**Theorem 4.3 (other-slot preservation).** *For distinct slots $s, s'$ and every case tag $t$,*
$$\pi_{M(s, t)}(T(s')) = T(s'). \tag{4.2}$$

This is *not* a consequence of the symmetry of §2; it is a property of the specific F-base sequences in §3, verified by inspection of the $60$ cases (4 slots $\times$ 3 distinct slots $\times$ 5 case tags).

The two corresponding statements about whiteness follow from the homomorphism $\pi_{c \cdot m} = \pi_c \circ \pi_m$:

**Corollary 4.4.** *Fix a state $c$, slot $s$, and case tag $t$.*

(i) *$W(c, S(s, t)) \implies W(c \cdot M(s, t),\, T(s))$.*

(ii) *For $s' \neq s$, $W(c \cdot M(s, t),\, T(s')) \iff W(c, T(s'))$.*

## §5. The algorithm

A state $c$ is **daisy-done**, written $D(c)$, if $W(c, T(s))$ holds for all four slots $s$.

The atomic step searches one slot through its case tags in the fixed order $F2, F6, R4, F8, D2$:

**Definition 5.1.** $\mathrm{trySlot}(c, s)$ returns

- nothing, if $W(c, T(s))$ (the slot is already done);
- $M(s, t)$, where $t$ is the first case tag with $W(c, S(s, t))$, if such a $t$ exists;
- nothing, otherwise.

Trying the four slots in the order UF, UR, UB, UL:

**Definition 5.2.** $\mathrm{trySlots}(c)$ returns the first non-empty value among $\mathrm{trySlot}(c, \mathrm{UF}), \mathrm{trySlot}(c, \mathrm{UR}), \mathrm{trySlot}(c, \mathrm{UB}), \mathrm{trySlot}(c, \mathrm{UL})$.

Some configurations admit no firing slot at the original orientation: a misplaced white edge may sit at a position covered only by an already-done slot. Pre-rotating the U face $k$ times reassigns which white sticker lies in which slot's coverage:

**Definition 5.3.** $\mathrm{tryRot}(c, k)$ returns the move sequence $U^k \cdot \mathrm{trySlots}(c \cdot U^k)$ if $\mathrm{trySlots}(c \cdot U^k)$ is non-empty, and nothing otherwise.

**Definition 5.4.** $\mathrm{tryFix}(c)$ returns the first non-empty value among $\mathrm{tryRot}(c, 0), \mathrm{tryRot}(c, 1), \mathrm{tryRot}(c, 2), \mathrm{tryRot}(c, 3)$, defaulting to the empty sequence if all four are empty.

The full algorithm runs four iterations:

**Definition 5.5.** Set $c_0 := c$, $m_i := \mathrm{tryFix}(c_{i-1})$ for $i = 1, 2, 3, 4$, and $c_i := c_{i-1} \cdot m_i$. Then
$$\mathrm{daisy}(c) := m_1 \cdot m_2 \cdot m_3 \cdot m_4.$$

The goal of the chapter is:

**Theorem (correctness).** *$D(c \cdot \mathrm{daisy}(c))$ for every state $c$.*

## §6. The white-target count

Define
$$N(c) := \big|\{ s \in \{\mathrm{UF}, \mathrm{UR}, \mathrm{UB}, \mathrm{UL}\} : W(c, T(s)) \}\big|.$$

Then $0 \leq N(c) \leq 4$, and $D(c)$ is equivalent to $N(c) = 4$.

Let $\tau$ be the cyclic permutation of slots $\mathrm{UF} \to \mathrm{UR} \to \mathrm{UB} \to \mathrm{UL} \to \mathrm{UF}$.

**Lemma 6.1.** *For every state $c$ and every slot $s$,*
$$W(c \cdot U,\, T(s)) \iff W(c,\, T(\tau(s))). \tag{6.1}$$

*Proof.* Direct computation: $\pi_U$ sends $T(s)$ to $T(\tau(s))$ for each of the four slots. $\blacksquare$

**Corollary 6.2.** *$N(c \cdot U^k) = N(c)$ for every $k \geq 0$.*

## §7. The step lemma

**Theorem 7.1 (step progress).** *Suppose $\neg W(c, T(s))$ and $W(c, S(s, t))$. Then*
$$N(c \cdot M(s, t)) = N(c) + 1. \tag{7.1}$$

*Proof.* By Corollary 4.4(i), the slot $s$ changes from non-white to white, contributing $+1$. By Corollary 4.4(ii), each indicator $W(\cdot, T(s'))$ for $s' \neq s$ is unchanged. $\blacksquare$

This propagates upward through the structure of $\mathrm{trySlot}$, $\mathrm{trySlots}$, and $\mathrm{tryRot}$ (using Corollary 6.2 to absorb the leading $U^k$):

**Theorem 7.2 (algorithm dichotomy).** *For every state $c$, either $\mathrm{tryFix}(c)$ is empty, or $N(c \cdot \mathrm{tryFix}(c)) = N(c) + 1$.*

## §8. Existence of a fire when not daisy-done

To rule out the empty disjunct of Theorem 7.2 unless the cube is already done, we establish:

**Theorem 8.1 (existence).** *$\neg D(c)$ implies $\mathrm{tryFix}(c)$ is non-empty.*

The proof has three structural ingredients: a pair-XOR lemma from the edge-flip identity (§8.1), Subclaim 1 forbidding white middle/D stickers under global failure (§8.2), and a pigeonhole on the four white-edge positions (§8.3).

### §8.1 Pair structure

Each U-pair is the two-element set
$$P(s) := \{T(s),\, S(s, F2)\},$$
and $S(s, F2) = T(s)^*$. (For $s = \mathrm{UF}$: $T(\mathrm{UF}) = (U, F)$ and $S(\mathrm{UF}, F2) = (F, U) = (U, F)^*$. The other three slots follow from §3.)

**Lemma 8.2 (pair-XOR).** *For every state $c$ and edge sticker $s$,*
$$\neg \big( W(c, s) \wedge W(c, s^*) \big). \tag{8.1}$$

*Proof.* If both held, the edge-flip identity (1.1) would force the two coordinates of $\pi_c(s)$ to both equal U; but the coordinates of an edge sticker are distinct. $\blacksquare$

In particular, each $P(s)$ contains at most one white sticker.

### §8.2 Subclaim 1: failure forbids middle/D whites

The $16$ stickers $S(s, t)$ with $t \in \{F6, R4, F8, D2\}$ are precisely the edge-stickers in the middle and bottom layers; we call them *middle/D positions*. They are characterized by being fixed by U:

**Lemma 8.3.** *For every $t \in \{F6, R4, F8, D2\}$, every slot $s$, and every $k \geq 0$,*
$$\pi_{U^k}(S(s, t)) = S(s, t).$$

*Proof.* The case $k = 1$ is by inspection of the action of $\pi_U$ on each of the $16$ middle/D positions. Induct on $k$. $\blacksquare$

**Theorem 8.4 (Subclaim 1).** *Suppose $\mathrm{tryRot}(c, k)$ is empty for $k = 0, 1, 2, 3$. If $W(c, S(s, t))$ for some $t \neq F2$, then $D(c)$.*

*Proof.* Fix $k \in \{0, 1, 2, 3\}$.

By Lemma 8.3, the position $S(s, t)$ is fixed by $U^k$, so
$$W(c \cdot U^k,\, S(s, t)) = W(c,\, S(s, t)) = \top. \tag{*}$$

The hypothesis $\mathrm{tryRot}(c, k) = \varnothing$ unfolds to $\mathrm{trySlots}(c \cdot U^k) = \varnothing$, hence $\mathrm{trySlot}(c \cdot U^k, s) = \varnothing$. Inspecting Definition 5.1: a non-empty source — which $(*)$ provides — forces the target to be already white. Therefore
$$W(c \cdot U^k,\, T(s)) = \top.$$

Iterating Lemma 6.1 gives the equivalent statement $W(c,\, T(\tau^k(s)))$. As $k$ ranges over $\{0, 1, 2, 3\}$, the value $\tau^k(s)$ ranges over all four slots, so every U-target is white in $c$, i.e. $D(c)$. $\blacksquare$

### §8.3 Pigeonhole on white-edge positions

For each slot $s$, the white edge originally labelled $T(s)$ now sits at the unique position
$$p_s := \pi_c^{-1}(T(s)).$$

Three structural properties:

(i) **Whiteness.** $W(c, p_s)$, since $\pi_c(p_s) = T(s)$ has first coordinate U.

(ii) **Distinctness.** $s \mapsto p_s$ is injective: the four labels $T(s)$ are distinct, and $\pi_c^{-1}$ is a bijection.

(iii) **Pair-distinctness.** For $s \neq s'$, $p_s \neq (p_{s'})^*$. For if equality held, applying $\pi_c$ and using (1.1) would give $T(s) = T(s')^*$; but $T(s)$ has first coordinate U while $T(s')^*$ has first coordinate the side label of $s'$, which is not U.

Now assume the failure hypothesis of §8.2 together with $\neg D(c)$. By Theorem 8.4 (contrapositively), no middle/D position is white in $c$; hence each $p_s$ lies in the *U-layer*
$$L := \bigcup_{s' \in \mathrm{Slot}} P(s').$$

The four U-pairs partition $L$. Define
$$\Pi : \mathrm{Slot} \to \mathrm{Slot}, \qquad \Pi(s) := \text{the unique } s' \text{ with } p_s \in P(s').$$

**Lemma 8.5.** *$\Pi$ is injective.*

*Proof.* Suppose $\Pi(s) = \Pi(s') = s''$ but $s \neq s'$. Then $p_s$ and $p_{s'}$ both lie in the two-element set $P(s'')$. Either

- $p_s = p_{s'}$, contradicting (ii); or
- $p_s$ and $p_{s'}$ are the two distinct elements of $P(s'')$, hence pair-partners ($p_s = (p_{s'})^*$), contradicting (iii). $\blacksquare$

**Corollary 8.6.** *$\Pi$ is a bijection.*

*Proof.* An injection from a finite set to itself is a bijection, and $|\mathrm{Slot}| = 4$. $\blacksquare$

### §8.4 Conclusion

*Proof of Theorem 8.1.* Suppose, towards a contradiction, that $\neg D(c)$ and $\mathrm{tryFix}(c)$ is empty.

(a) **$\mathrm{tryRot}(c, k)$ returns nothing for each $k = 0, 1, 2, 3$.** Whenever $\mathrm{tryRot}(c, k)$ does return a move sequence $m$, that sequence is non-empty as a list: the building block of Theorem 7.2 gives $N(c \cdot m) = N(c) + 1$, so $m$ cannot be the empty list (which would act as the identity). Now $\mathrm{tryFix}(c)$ returns the first such $m$, defaulting to the empty list only when all four $\mathrm{tryRot}(c, k)$ return nothing. By assumption $\mathrm{tryFix}(c)$ is the empty list, ruling out the first alternative.

(b) Choose a *failed slot*: $\neg D(c)$ yields a slot $s_*$ with $\neg W(c, T(s_*))$.

(c) By Corollary 8.6, choose $s_{**}$ with $\Pi(s_{**}) = s_*$. Then $p_{s_{**}} \in P(s_*) = \{T(s_*),\, S(s_*, F2)\}$.

(d) By (i), $W(c, p_{s_{**}})$. Since $\neg W(c, T(s_*))$, we must have
$$p_{s_{**}} = S(s_*, F2), \qquad \text{hence} \qquad W(c, S(s_*, F2)).$$

(e) Consulting Definition 5.1 for $\mathrm{trySlot}(c, s_*)$: the target $T(s_*)$ is non-white (b), and the F2-source $S(s_*, F2)$ is white (d). The first if-then-else returns $M(s_*, F2)$, which is non-empty. Hence $\mathrm{trySlots}(c)$ is non-empty, so $\mathrm{tryRot}(c, 0)$ is non-empty, contradicting (a). $\blacksquare$

## §9. Main theorem

**Theorem 9.1 (single-step progress with cap).** *For every state $c$,*
$$N(c \cdot \mathrm{tryFix}(c)) \geq \min(N(c) + 1,\; 4). \tag{9.1}$$

*Proof.* By Theorem 7.2 the count either jumps by exactly one or $\mathrm{tryFix}(c)$ is empty. In the latter case Theorem 8.1 forces $D(c)$, hence $N(c) = 4$, and the right-hand side of (9.1) equals $4 = N(c)$. $\blacksquare$

**Theorem 9.2 (four-step closure).** *Setting $c_0 := c$ and $c_i := c_{i-1} \cdot \mathrm{tryFix}(c_{i-1})$ for $i = 1, 2, 3, 4$,*
$$N(c_4) = 4.$$

*Proof.* Apply Theorem 9.1 four times:
$$N(c_i) \geq \min(N(c_{i-1}) + 1,\; 4) \qquad (i = 1, 2, 3, 4),$$
combined with $N(c_4) \leq 4$. The integer arithmetic forces $N(c_4) = 4$. $\blacksquare$

**Theorem 9.3 (correctness of the Daisy algorithm).** *For every state $c$,*
$$D(c \cdot \mathrm{daisy}(c)).$$

*Proof.* The homomorphism $c \cdot (m \cdot m') = (c \cdot m) \cdot m'$ applied repeatedly aligns $c \cdot \mathrm{daisy}(c)$ with $c_4$. Theorem 9.2 yields $N(c_4) = 4$, equivalent to $D(c_4)$. $\blacksquare$
