# Three Sphere

- The commutation relations between $k_3$, $k_+$, and $k_-$ are shown in [Operator.lean](./Sphere/Operator.lean).
- Flatness of the connection is shown in [Flatness.lean](./Sphere/Flatness.lean), and the exterior derivatives of $\alpha$, $\lambda$, and $\bar{\lambda}$ are computed in [Differential.lean](./Sphere/Differential.lean).
- That $(\rho, \phi, \bar{\phi})$ and $(\alpha, \lambda, \bar{\lambda})$ are dual is shown in [Duality.lean](./Sphere/Duality.lean).
- The Lie derivative relations between $\rho$, $\phi$, and $\bar{\phi}$ are computed in [Lie.lean](./Sphere/Lie.lean).

# Seven Sphere

- The representation of $S^7$ as unit two components quaternionic vector is defined in [Seven/Basis.lean](./Sphere/Seven/Basis.lean) along with the exterior algebra on $S^7$.
  A basis for $\mathfrak{u}_2(\mathbb{H})$ is also defined.
- The calculation of the 10 fundamental vector fields induced by a basis for $\mathfrak{u}_2(\mathbb{H})$ is in [Seven/Fundamental.lean](./Sphere/Seven/Fundamental.lean).
- The interior product between the fundamental vector fields with $\alpha$ and $d\alpha$ are calculated in [Seven/Alpha.lean](./Sphere/Seven/Alpha.lean) and [Seven/DifferentialAlpha.lean](./Sphere/Seven/Alpha.lean), respectively.
  The Lie derivatives of $\alpha$ along those vector fields are calculated in [Seven/Lie.lean](./Sphere/Seven/Lie.lean).
- An explicit formula for the Reeb vector field  is shown in [Seven/Reeb.lean](./Sphere/Seven/Reeb.lean).