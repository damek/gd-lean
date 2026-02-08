# Gradient Descent Blueprint Prompt

This file records exactly what was sent to Aristotle from Harmonic.

- Model used: GPT-5.2 Pro (Extended Thinking)
- Notes: The response below is kept verbatim (no manual edits)

## Prompt Sent to GPT-5.2 Pro

```text
I want to prove the standard 1/k convergence rate for gradient descent on a convex function $f$ with L-Lipschitz continuous gradient.

x_{k+1} = x_k - \eta \nabla f(x_k)

Can you please write up a highly detailed blue print of the argument that I can feed to an autoformalization agent. It should include: 
- Formalization of the descent lemma for function with L-lipschitz gradients. 
- A proof the bound f(x_k) - f^\ast \leq C/(k+1) with explicit constant C determined by lipschitz constant, stepsize \eta > 0, and the distance of the initial iterate to the minimizer. 
```

## GPT-5.2 Pro Response (Verbatim)

```text
**Key deliverable:** a formal, step-by-step blueprint proving the **descent lemma** and the **(O(1/k))** rate for gradient descent on **convex (L)-smooth** (f), with an **explicit constant** in terms of (L), (\eta), and (|x_0-x^*|).

**Confidence:** very high (standard smooth convex GD proof; only “off-by-one indexing” conventions vary).

**Limits / conventions:** I’ll assume Euclidean space (\mathbb{R}^d) (or a real Hilbert space), and that a minimizer (x^*\in\arg\min f) exists. The cleanest last-iterate (1/k) proof below uses the standard stepsize condition
[
0<\eta\le \frac1L.
]
For (\eta>1/L), the monotonicity and the inequality that makes the telescope work can fail.

---

## 0. Formal setup (objects, assumptions, notation)

### Ambient space

* Let ((\mathbb{R}^d,\langle\cdot,\cdot\rangle,|\cdot|)) be Euclidean space.
* You can generalize verbatim to a real Hilbert space.

### Function class

Let (f:\mathbb{R}^d\to\mathbb{R}) satisfy:

1. **Convexity:**
   [
   \forall x,y,\ \forall t\in[0,1],\quad f((1-t)x+ty)\le (1-t)f(x)+t f(y).
   ]

2. **Differentiability:** (f) is (Fréchet) differentiable everywhere with gradient (\nabla f(x)).

3. **(L)-Lipschitz gradient (a.k.a. (L)-smoothness):** there exists (L>0) such that
   [
   \forall x,y,\quad |\nabla f(x)-\nabla f(y)|\le L|x-y|.
   ]
   (In autoformalization, you often name this `L_smooth`.)

4. **Attainment of optimum:** assume there exists (x^*\in\mathbb{R}^d) such that
   [
   f(x^*) = f^* := \inf_{x} f(x).
   ]
   Under convexity + smoothness, first-order optimality gives (\nabla f(x^*)=0).

### Algorithm

Given stepsize (\eta>0),
[
x_{k+1} := x_k - \eta \nabla f(x_k),\qquad k=0,1,2,\dots
]

Goal: prove
[
f(x_k)-f^* \le \frac{C}{k+1}
]
with explicit (C) depending only on (L,\eta,|x_0-x^*|), under (0<\eta\le 1/L).

---

## 1. Core lemma: Descent lemma for (L)-Lipschitz gradients

### Statement (Descent Lemma / Smooth upper quadratic bound)

**Lemma (Descent lemma).**
Assume (\nabla f) is (L)-Lipschitz. Then for all (x,y\in\mathbb{R}^d),
[
f(y)\le f(x) + \langle \nabla f(x),, y-x\rangle + \frac{L}{2}|y-x|^2.
\tag{DL}
]

This is the exact lemma you’ll use to get one-step decrease for gradient descent.

---

### Formal proof blueprint of (DL)

This proof is “line integral + Lipschitz gradient bound”. It’s friendly to formalization.

**Step DL.1 (Reduce to 1D along the segment).**
Fix (x,y). Define the scalar function (\varphi:[0,1]\to\mathbb{R}) by
[
\varphi(t) := f(x+t(y-x)).
]
Then (\varphi(0)=f(x)) and (\varphi(1)=f(y)).

**Step DL.2 (Differentiate (\varphi) via chain rule).**
Since (f) is differentiable, (\varphi) is differentiable with
[
\varphi'(t) = \langle \nabla f(x+t(y-x)),, y-x\rangle.
]

**Step DL.3 (Fundamental theorem of calculus).**
[
f(y)-f(x) = \varphi(1)-\varphi(0)=\int_0^1 \varphi'(t),dt
= \int_0^1 \langle \nabla f(x+t(y-x)),, y-x\rangle,dt.
]

**Step DL.4 (Add and subtract (\nabla f(x)) inside the integral).**
[
\begin{aligned}
f(y)-f(x)
&= \int_0^1 \langle \nabla f(x),, y-x\rangle,dt

* \int_0^1 \langle \nabla f(x+t(y-x))-\nabla f(x),, y-x\rangle,dt\
  &= \langle \nabla f(x),, y-x\rangle
* \int_0^1 \langle \nabla f(x+t(y-x))-\nabla f(x),, y-x\rangle,dt.
  \end{aligned}
  ]

**Step DL.5 (Apply Cauchy–Schwarz + Lipschitz gradient).**
For each (t\in[0,1]),
[
\langle \nabla f(x+t(y-x))-\nabla f(x),, y-x\rangle
\le |\nabla f(x+t(y-x))-\nabla f(x)|\cdot|y-x|.
]
Using Lipschitz gradient with points (x+t(y-x)) and (x):
[
|\nabla f(x+t(y-x))-\nabla f(x)|
\le L |t(y-x)| = Lt|y-x|.
]
Hence the integrand is bounded by (Lt|y-x|^2).

**Step DL.6 (Integrate the bound).**
[
\int_0^1 Lt|y-x|^2,dt = L|y-x|^2\int_0^1 t,dt = \frac{L}{2}|y-x|^2.
]

**Step DL.7 (Assemble).**
[
f(y)-f(x) \le \langle \nabla f(x),, y-x\rangle + \frac{L}{2}|y-x|^2.
]
Rearrange to get (DL).

That completes the formal proof.

---

## 2. One-step decrease for gradient descent (plug (y=x-\eta\nabla f(x)))

### Statement

**Lemma (GD decrease via descent lemma).**
If (\nabla f) is (L)-Lipschitz, then for any (x) and any (\eta>0),
[
f\bigl(x-\eta\nabla f(x)\bigr)
\le f(x) - \eta\Bigl(1-\frac{L\eta}{2}\Bigr)|\nabla f(x)|^2.
\tag{GD-Desc}
]
In particular, if (0<\eta\le 1/L), then (1-\tfrac{L\eta}{2}\ge \tfrac12), so
[
f(x-\eta\nabla f(x))\le f(x) - \frac{\eta}{2}|\nabla f(x)|^2,
\tag{GD-Desc-1/2}
]
and thus (f(x_{k+1})\le f(x_k)): monotone decrease.

### Proof blueprint

Apply (DL) with (y=x-\eta\nabla f(x)). Then (y-x=-\eta\nabla f(x)). So

[
\begin{aligned}
f(x-\eta\nabla f(x))
&\le f(x)+\langle \nabla f(x), -\eta\nabla f(x)\rangle + \frac{L}{2}|,-\eta\nabla f(x)|^2\
&= f(x) - \eta|\nabla f(x)|^2 + \frac{L\eta^2}{2}|\nabla f(x)|^2\
&= f(x) - \eta\Bigl(1-\frac{L\eta}{2}\Bigr)|\nabla f(x)|^2.
\end{aligned}
]

---

## 3. Convexity inequality you’ll telescope with

### Statement (First-order convexity inequality)

If (f) is convex and differentiable, then for all (x,y),
[
f(y)\ge f(x)+\langle \nabla f(x),, y-x\rangle.
\tag{FOC}
]
Equivalently,
[
f(x)-f(y)\le \langle \nabla f(x),, x-y\rangle.
\tag{FOC'}
]

Specialize to (y=x^*) to get:
[
f(x)-f^*\le \langle \nabla f(x),, x-x^*\rangle.
\tag{Gap≤Inner}
]

### Proof blueprint (quick)

Convex differentiable implies the gradient is a subgradient at every point; i.e., (\nabla f(x)\in\partial f(x)), and the subgradient inequality is exactly (FOC). In Euclidean formalizations, this is typically a standard lemma: `convex` + `differentiable` → `subgradient` → `supporting_hyperplane`.

---

## 4. Key inequality linking function gap to squared distance drop

This is the crucial inequality that telescopes and yields (1/k).

### Lemma (Single-step gap bound by distance decrease)

Assume:

* (f) convex and differentiable,
* (\nabla f) (L)-Lipschitz,
* (0<\eta\le 1/L),
* (x_{k+1}=x_k-\eta\nabla f(x_k)),
* (x^*\in\arg\min f).

Then for every (k\ge 0),
[
f(x_{k+1})-f^*
\le \frac{1}{2\eta}\Bigl(|x_k-x^*|^2-|x_{k+1}-x^*|^2\Bigr).
\tag{Tel}
]

This is the inequality you sum over (k).

---

### Proof blueprint of (Tel)

**Step T.1 (Expand the squared distance).**
Using (x_{k+1}=x_k-\eta\nabla f(x_k)),
[
\begin{aligned}
|x_{k+1}-x^*|^2
&= |x_k-\eta\nabla f(x_k)-x^*|^2\
&= |x_k-x^*|^2 - 2\eta\langle \nabla f(x_k), x_k-x^*\rangle + \eta^2|\nabla f(x_k)|^2.
\end{aligned}
]
Rearrange:
[
2\eta\langle \nabla f(x_k), x_k-x^*\rangle
= |x_k-x^*|^2 - |x_{k+1}-x^*|^2 + \eta^2|\nabla f(x_k)|^2.
\tag{DistId}
]

**Step T.2 (Use convexity to lower bound the inner product).**
From (Gap≤Inner) with (x=x_k):
[
f(x_k)-f^*\le \langle \nabla f(x_k), x_k-x^*\rangle.
]
Multiply by (2\eta):
[
2\eta(f(x_k)-f^*) \le 2\eta\langle \nabla f(x_k), x_k-x^*\rangle.
\tag{Cv1}
]

**Step T.3 (Substitute (DistId) into (Cv1)).**
[
2\eta(f(x_k)-f^*)
\le |x_k-x^*|^2 - |x_{k+1}-x^*|^2 + \eta^2|\nabla f(x_k)|^2.
]
Divide by (2\eta):
[
f(x_k)-f^*
\le \frac{1}{2\eta}\bigl(|x_k-x^*|^2 - |x_{k+1}-x^*|^2\bigr)

* \frac{\eta}{2}|\nabla f(x_k)|^2.
  \tag{Cv2}
  ]

**Step T.4 (Upper bound the gradient term by the actual function decrease).**
From (GD-Desc-1/2) applied at (x_k) (valid since (\eta\le 1/L)):
[
f(x_{k+1}) \le f(x_k) - \frac{\eta}{2}|\nabla f(x_k)|^2.
]
Rearrange:
[
\frac{\eta}{2}|\nabla f(x_k)|^2 \le f(x_k)-f(x_{k+1}).
\tag{Grad≤Dec}
]

**Step T.5 (Plug (Grad≤Dec) into (Cv2)).**
[
f(x_k)-f^*
\le \frac{1}{2\eta}\bigl(|x_k-x^*|^2 - |x_{k+1}-x^*|^2\bigr)

* \bigl(f(x_k)-f(x_{k+1})\bigr).
  \tag{Cv3}
  ]

**Step T.6 (Cancel (f(x_k)) to isolate (f(x_{k+1})-f^*)).**
Subtract (f(x_k)-f(x_{k+1})) from both sides of (Cv3):
[
f(x_{k+1})-f^*
\le \frac{1}{2\eta}\bigl(|x_k-x^*|^2 - |x_{k+1}-x^*|^2\bigr).
]
That is exactly (Tel).

---

## 5. Telescope and conclude the (1/k) rate with explicit constant

### Step R.1 (Sum (Tel) over (k))

Sum (Tel) for (k=0,1,\dots,K):
[
\sum_{k=0}^{K}\bigl(f(x_{k+1})-f^*\bigr)
\le \frac{1}{2\eta}\sum_{k=0}^{K}\Bigl(|x_k-x^*|^2-|x_{k+1}-x^*|^2\Bigr).
]
The right-hand side telescopes:
[
\sum_{k=0}^{K}\Bigl(|x_k-x^*|^2-|x_{k+1}-x^*|^2\Bigr)
= |x_0-x^*|^2 - |x_{K+1}-x^*|^2
\le |x_0-x^*|^2.
]
Therefore
[
\sum_{k=0}^{K}\bigl(f(x_{k+1})-f^*\bigr)
\le \frac{|x_0-x^*|^2}{2\eta}.
\tag{SumBound}
]

### Step R.2 (Use monotonicity to bound the last iterate)

From (GD-Desc-1/2), the sequence (f(x_k)) is non-increasing for (\eta\le 1/L), hence
[
f(x_{K+1})-f^* \le f(x_{k+1})-f^*\quad\text{for all }k=0,\dots,K.
]
So each term in the sum is (\ge f(x_{K+1})-f^*), giving
[
(K+1)\bigl(f(x_{K+1})-f^*\bigr)
\le \sum_{k=0}^{K}\bigl(f(x_{k+1})-f^*\bigr).
\tag{MonAvg}
]
Combine (MonAvg) with (SumBound):
[
(K+1)\bigl(f(x_{K+1})-f^*\bigr)
\le \frac{|x_0-x^*|^2}{2\eta}.
]
Divide by (K+1):
[
f(x_{K+1})-f^*
\le \frac{|x_0-x^*|^2}{2\eta (K+1)}.
\tag{RateShifted}
]

### Step R.3 (Match indexing to the user’s “(k+1)” form)

Let (k:=K+1) (so (k\ge 1)). Then (RateShifted) reads:
[
f(x_k)-f^* \le \frac{|x_0-x^*|^2}{2\eta, k},\qquad k\ge 1.
\tag{Rate1overk}
]

If you prefer the exactly requested format (\frac{C}{k+1}) for (k\ge 0), just rewrite with (k\mapsto k+1):
[
f(x_{k+1})-f^* \le \frac{|x_0-x^*|^2}{2\eta (k+1)},\qquad k\ge 0.
\tag{RateC/(k+1)}
]

This is the clean “(1/(k+1))” statement with an explicit constant.

---

## 6. Explicit constant (C)

Under assumptions above, for all (k\ge 0),
[
f(x_{k+1})-f^* \le \frac{C}{k+1}
\quad\text{with}\quad
C := \frac{|x_0-x^*|^2}{2\eta},
\qquad 0<\eta\le\frac1L.
]

So (C) depends exactly on (\eta) and the initial distance to a minimizer. The dependence on (L) is through the admissible range of (\eta).

**Specialization to (\eta=1/L):**
[
f(x_{k+1})-f^* \le \frac{L}{2}\frac{|x_0-x^*|^2}{k+1}.
]

---

## 7. “Formalization checklist” (for an autoformalization agent)

Below is a minimal dependency graph of lemmas you should ask the agent to formalize.

### Definitions

1. `convex f` (Jensen inequality).
2. `grad_lipschitz f L` meaning (|\nabla f(x)-\nabla f(y)|\le L|x-y|).
3. `gradient_descent_step η x := x - η ∇f(x)` and iterate definition.

### Lemmas (in recommended order)

**(L1) Fundamental theorem along a segment.**
For (\varphi(t)=f(x+t(y-x))), show
(f(y)-f(x)=\int_0^1 \langle \nabla f(x+t(y-x)), y-x\rangle dt).

**(L2) Descent lemma (DL).**
Using (L1) + Cauchy–Schwarz + Lipschitz gradient + (\int_0^1 tdt=1/2).

**(L3) GD decrease (GD-Desc).**
Plug (y=x-\eta\nabla f(x)) into (DL) and simplify.

**(L4) Monotonicity for (\eta\le 1/L).**
From (GD-Desc) show (f(x_{k+1})\le f(x_k)).

**(L5) First-order convexity inequality (FOC).**
Convex differentiable implies supporting hyperplane inequality:
(f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle).
Specialize to (y=x^*) to get (f(x)-f^*\le\langle\nabla f(x),x-x^*\rangle).

**(L6) Squared distance identity.**
Expand (|x_{k+1}-x^*|^2) and derive (DistId).

**(L7) Combine (L5)+(L6)+(L3 with (\eta\le 1/L)) to prove (Tel).**
This is the key formal step.

**(L8) Telescope sum.**
Sum (Tel) from (k=0) to (K) and simplify.

**(L9) Convert sum bound to last-iterate bound.**
Use monotonicity (L4) to infer ((K+1)(f(x_{K+1})-f^*)\le \sum_{k=0}^K (f(x_{k+1})-f^*)).

### Final theorem

Combine (L8)+(L9) to conclude:
[
f(x_{K+1})-f^*\le \frac{|x_0-x^*|^2}{2\eta(K+1)}.
]

---

## 8. Optional add-on: bounding (f(x_0)-f^*) by (|x_0-x^*|^2)

If you want a clean statement that also covers (k=0) with the same constant (sometimes helpful for uniform indexing), you can use (DL) with (x=x^*), (y=x_0) and (\nabla f(x^*)=0):
[
f(x_0)-f^*\le \frac{L}{2}|x_0-x^*|^2.
]
If (\eta\le 1/L), then (\frac{L}{2}|x_0-x^*|^2 \le \frac{1}{2\eta}|x_0-x^*|^2=C), so
[
f(x_0)-f^*\le C.
]
This lets you state “for all (k\ge 0), (f(x_k)-f^*\le C/(k+1))” **if** you’re willing to accept the minor index-shift looseness (since the tight derivation naturally controls (x_{k+1}) by (k+1)).

---

If you tell me what proof primitives your autoformalization agent prefers (e.g., integration vs. mean-value theorem; Hilbert space vs. (\mathbb{R}^d); whether you already have convex-subgradient lemmas), I can rewrite the blueprint into a “lemma-by-lemma script” with explicit dependencies and no prose.
```
