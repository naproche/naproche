[synonym number/-s]
[prover vampire]
[read macros.ftl]
################################################
Let z << M stand for z is in M.

Let f denote a function.
Let M denote a class.

Lemma. Every set is a class.

Definition.
A subset of M is a set N such that every element of N is an element of M.
Let N \subseteq M stand for N is a subset of M.

Definition.
Assume M is a subset of the domain of f. f[M] = { f(x) | x << M }.

Axiom.
Assume M is a subset of the domain of f. Then f[M] is a set.

Definition. Let U be a subset of the domain of f. f is constant on U iff
there exists an object z such that f(w) = z for every element w of U.
Let f is constant stand for f is constant on the domain of f.


################################################

Signature. A complex number is an object.
Let z,w denote complex numbers.

Definition. CC is the collection of all complex numbers.

Axiom. CC is a set.

Signature.
A real number is a complex number.
Let x, y denote real numbers.

Signature. |z| is a real number.

Signature. x is positive is an atom.
Let eps, delta denote positive real numbers.

Signature. x < y is an atom.
Let x > y stand for y < x.
Let x =< y stand for x = y or x < y.

Axiom. x < y => not y < x.

Signature. Ball(eps,z) is a subset of CC that contains z.

Axiom. |z| < |w| for some element w of Ball(eps,z).

Definition. Let M be a subset of CC. M is open iff for every element z of M
there exists eps such that Ball(eps,z) is a subset of M.

Axiom. Ball(eps,z) is open.

Signature.
A region is an open subset of CC.

Signature. Let M be a region. M is simply connected is an atom.


Signature. A holomorphic function is a function f such that
Dom(f) \subseteq CC and f(w) << CC for every element w of Dom(f).

Let f denote a holomorphic function.

Definition. A local maximal point of f is an element z of the domain of f such that there
exists eps such that Ball(eps,z) is a subset of the domain of f and
|f(w)|=< |f(z)| for every element w of Ball(eps,z).

Axiom. Assume f is a holomorphic function and Ball(eps,z) is a subset of the domain of f.
If f is not constant on Ball(eps,z) then f[Ball(eps,z)] is open.

Axiom Identity_Theorem
Assume f is a holomorphic function and the domain of f is a simply connected region.
Assume that Ball(eps,z) is a subset of the domain of f.
If f is constant on Ball(eps,z) then f is constant.


Proposition Maximum_principle.
Assume f is a holomorphic function and the domain of f is a simply connected region.
If f has a local maximal point then f is constant.
Proof.
Let z be a local maximal point of f. Take eps such that
Ball(eps,z) is a subset of Dom(f) and |f(w)| =< |f(z)| for every element w of Ball(eps,z).
Let us show that f is constant on Ball(eps,z).
	proof by contradiction.
	Assume the contrary. Then f[Ball(eps,z)] is open. We can take delta such that
Ball(delta, f(z)) is a subset of f[Ball(eps,z)].
	Therefore there exists an element w of Ball(eps,z) such that |f(w)| > |f(z )|. Contradiction.
	end.
Hence f is constant.
qed.
