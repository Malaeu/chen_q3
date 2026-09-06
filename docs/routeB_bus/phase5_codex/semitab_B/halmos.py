"""S3 sanity: the exact Halmos plant of the verdict, eq. (10)."""
import numpy as np
from fractions import Fraction as Fr

a = Fr(3, 5); s = Fr(4, 5)
P = np.array([[Fr(1), Fr(0)], [Fr(0), Fr(0)]], dtype=object)
Q = np.array([[a * a, a * s], [a * s, s * s]], dtype=object)
D = np.array([[a * a, a * s], [a * s, -a * a]], dtype=object)
I = np.array([[Fr(1), Fr(0)], [Fr(0), Fr(1)]], dtype=object)
v = np.array([Fr(2), Fr(1)], dtype=object)                  # /sqrt5
M = I - P - Q
val = sum(v[i] * M[i, j] * v[j] for i in range(2) for j in range(2)) / Fr(5)
print("I - P - Q =", M.tolist())
print("<v,(I-P-Q)v> with v=(2,1)/sqrt5 :", val, " (verdict (10) says -3/5)")
print("D_S block eigenvalues:", sorted(np.linalg.eigvalsh(np.array(D, dtype=float))))
print("S v = (I-P-Q+D) v =", [sum((M[i, j] + D[i, j]) * v[j] for j in range(2)) for i in range(2)],
      " (verdict (10) says S v = 0)")
print("Q idempotent:", np.allclose(np.array(Q, dtype=float) @ np.array(Q, dtype=float),
                                   np.array(Q, dtype=float)))
