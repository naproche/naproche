[synonym number/-s]

Let the domain of f stand for Dom(f).
Let z is in M stand for z is an element of M.
Let M contains z stand for z is in M.
Let z << M stand for z is in M.

Let f denote a function.
Let M denote a set.

Definition.
A subset of M is a set N such that every element of N is an element of M.

Definition.
Assume M is a subset of the domain of f. f^[M] = { f[x] | x << M }.

Signature. A complex number is a notion.

Let z,w denote complex numbers.

Axiom.
Every element of Dom(f) is a complex number and for every element z of Dom(f) f[z] is a complex number.

Axiom.
Every element of M is a complex number.

Signature.
A real number is a notion.
Let x, y denote real numbers.

Signature. |z| is a real number.

Signature. x is positive is an atom.
Let eps, delta denote positive real numbers.

Signature. x < y is an atom.
Let x =< y stand for x = y or x < y.

Axiom. x < y => not y < x.

Signature. f is holomorphic is an atom.

Signature. Ball(eps,z) is a set that contains z.

Axiom. |z| < |w| for some element w of Ball(eps,z).

Definition. M is open iff for every element z of M there exists eps such that Ball(eps,z) is a subset of M.

Axiom. Ball(eps,z) is open.

Definition. A local maximal point of f is an element z of the domain of f such that there exists eps such that Ball(eps,z)
            is a subset of the domain of f and |f[w]|=< |f[z]| for every element w of Ball(eps,z).

Definition. Let U be a subset of the domain of f. f is constant on U iff there exists z such that f[w] = z for every element w of U.
Let f is constant stand for f is constant on the domain of f.


Axiom. Assume f is holomorphic and Ball(eps,z) is a subset of the domain of f. If f is not constant on Ball(eps,z) then f^[Ball(eps,z)] is open.

Signature.
A region is an open set.

Axiom Identity_Theorem.
Assume f is holomorphic and the domain of f is a region. Assume that Ball(eps,z) is a subset of the domain of f. If f is constant on Ball(eps,z) then f is constant.


Proposition Maximum_principle.
Assume f is holomorphic and the domain of f is a region. If f has a local maximal point then f is constant.
Proof.
Let z be a local maximal point of f. Take eps such that Ball(eps,z) is a subset of Dom(f) and |f[w]| =< |f[z]| for every element w of Ball(eps,z).
Let us show that f is constant on Ball(eps,z).
	proof by contradiction.
	Assume the contrary. Then f^[Ball(eps,z)] is open. We can take delta such that Ball(delta, f[z]) is a subset of f^[Ball(eps,z)].
	Therefore there exists an element w of Ball(eps,z) such that |f[z]| < |f[w]|. Contradiction.
	end.
Hence f is constant.
qed.
