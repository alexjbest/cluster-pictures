from copy import copy
from collections import defaultdict
from sage.misc.html import HtmlFragment
from sage.rings.all import Infinity, PolynomialRing, QQ, RDF, ZZ
from sage.all import SageObject, Matrix, verbose, ascii_art


def allroots(f):
    while True:
        roots = f.roots()
        if sum(d for _, d in roots) == f.degree():
            return sum([d*[r] for r, d in roots], [])
        _, g = min([(g.degree(), g) for g, d in f.factor() if g.degree() > 1])
        K = g.root_field('a')
        f = f.change_ring(K)
    return roots


class Cluster(SageObject):
    r"""
    Construct a cluster picture.

    INPUT:

    - ``A`` -- a matrix of valuations of differences of roots

    EXAMPLES:

    Example 1.2 from M2D2::

        sage: from sage_cluster_pictures.cluster_pictures import Cluster
        sage: p = 7
        sage: x = polygen(Qp(p))
        sage: H = HyperellipticCurve((x-1)*(x-(1+p^2))*(x-(1-p^2))*(x-p)*x*(x-p^3)*(x+p^3))
        sage: C = Cluster.from_curve(H)
        sage: print(ascii_art(C))
        ((* * *) *) (* * *)

    """

    def __init__(self, M, parent=None):
        r"""
        See :class:`Cluster` for documentation.

        TESTS::

            sage: C = Cluster()
            sage: TestSuite(C).run()
        """
        verbose(M)
        self._M = M
        self._size = M.nrows()
        self._parent_cluster = parent
        depth = self.depth()
        verbose(depth)
        children = defaultdict(list)
        for r1 in range(self._size):
            if r1 not in sum(children.values(), []):
                for r2 in range(r1, self._size):
                    if M[r1, r2] > depth:
                        children[r1] += [r2]
        verbose(children)
        self._children = [Cluster(M.matrix_from_rows_and_columns(rs, rs),
                                  parent=self) for c, rs in children.items()]

    @classmethod
    def from_roots(cls, roots):
        r"""
        Construct a Cluster from a list of roots.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: Cluster.from_roots([K(1), K(5), K(10)])
            Cluster with 3 roots

        """
        K = roots[0].parent()
        return cls(Matrix([[(r1-r2).add_bigoh(K.precision_cap()).valuation()
                            for r1 in roots] for r2 in roots]))

    @classmethod
    def from_curve(cls, H):
        if H.hyperelliptic_polynomials()[1] != 0:
            raise ValueError("Curve must be of the form y^2 = f(x)")
        return cls.from_roots(allroots(H.hyperelliptic_polynomials()[0]))


    def parent_cluster(self):
        return self._parent_cluster

    def depth(self):
        return min(self._M.dense_coefficient_list())

    def relative_depth(self):
        return self.depth() - self.parent().depth()

    def size(self):
        return self._size

    def is_even(self):
        r"""
        Check if the Cluster is even.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.is_even()
            False
            sage: C = Cluster.from_roots([K(1), K(2), K(5), K(10)])
            sage: C.is_even()
            True
            sage: C = Cluster.from_roots([K(1), K(6), K(5), K(10)])
            sage: C.is_even()
            True

        """
        return self.size() % 2 == 0

    def is_odd(self):
        r"""
        Check if the Cluster is odd.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.is_odd()
            True
            sage: C = Cluster.from_roots([K(1), K(2), K(5), K(10)])
            sage: C.is_odd()
            False
            sage: C = Cluster.from_roots([K(1), K(6), K(5), K(10)])
            sage: C.is_odd()
            False

        """
        return not self.is_even()

    def is_proper(self):
        return self.size() > 1

    def children(self):
        return self._children

    def num_children(self):
        return len(self.children())

    def all_descendents(self):
        for C in self.children():
            yield C
            yield from C.children() 

    def is_ubereven(self):
        r"""
        Check if the Cluster is übereven.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.is_ubereven()
            False
            sage: C = Cluster.from_roots([K(1), K(2), K(5), K(10)])
            sage: C.is_ubereven()
            False
            sage: C = Cluster.from_roots([K(1), K(6), K(5), K(10)])
            sage: C.is_ubereven()
            True

        """
        return all(C.is_even() for C in self.children())

    def __eq__(self, other):
        r"""
        Check if two Clusters are equal.

        INPUT:

        - ``other`` -- anything

        OUTPUT:

        - ``True`` if ``other`` is an :class:`InteractiveLPProblem` with all details the
          same as ``self``, ``False`` otherwise.

        TESTS::

            sage: from sage_numerical_interactive_mip import InteractiveMILPProblem
            sage: A = ([1, 1], [3, 1])
        """
        return (isinstance(other, InteractiveMILPProblem) and
                self._relaxation == other._relaxation and
                self._integer_variables == other._integer_variables)

    def _ascii_art_(self):
        r"""
        Return an ascii art representation of ``self``.
        """

        if not self.is_proper():
            return "*"
        return " ".join(("(%s)" if c.is_proper() else "%s") % ascii_art(c) for c in self.children())

    def _latex_(self):
        r"""
        Return a LaTeX representation of ``self``.

        OUTPUT:

        - a string

        """
        lines = self.relaxation()._latex_()
        integer_var = ""
        continuous_var = ""
        if self.integer_variables():
            integer_var =  r"{} \in {}".format(
                                   ", ".join(map(latex, sorted(self.integer_variables()))),
                                    r"\mathbb{Z}") +  r" \\"
        if self.continuous_variables():
            continuous_var =  r"{} \in {}".format(
                                   ", ".join(map(latex, sorted(self.continuous_variables()))),
                                    r"\mathbb{R}")
        return lines[:-11] + r" \\" + integer_var + continuous_var + lines[-11:]

    def _repr_(self):
        r"""
        Return a string representation of ``self``.

        OUTPUT:

        - a string

        TESTS::

            sage: from sage_numerical_interactive_mip import InteractiveMILPProblem
            sage: A = ([1, 1], [3, 1])
            sage: b = (1000, 1500)
            sage: c = (10, 5)
            sage: P = InteractiveMILPProblem(A, b, c, variable_type=">=", integer_variables={"x1"})
            sage: print(P._repr_())
            MILP problem (use typeset mode to see details)
        """
        return "Cluster with %s roots and %s children" % (self.size(), self.num_children())

    def is_principal(self):
        r"""
        Check if ``self`` is principal.
        """
        raise NotImplementedError("this method is not implemented, yet")

    def plot(self, *args, **kwds):
        r"""
        Return a plot for solving ``self`` graphically.

        INPUT:

        - ``xmin``, ``xmax``, ``ymin``, ``ymax`` -- bounds for the axes, if
          not given, an attempt will be made to pick reasonable values

        - ``alpha`` -- (default: 0.2) determines how opaque are shadows

        OUTPUT:

        - a plot

        .. NOTE::

            This only works for problems with two decision variables.
            On the plot the black arrow indicates the direction of growth
            of the objective. The lines perpendicular to it are level
            curves of the objective. If there are optimal solutions, the
            arrow originates in one of them and the corresponding level
            curve is solid: all points of the feasible set on it are optimal
            solutions. Otherwise the arrow is placed in the center. If the
            problem is infeasible or the objective is zero, a plot of the
            feasible set only is returned.

        EXAMPLES::

            sage: from sage_numerical_interactive_mip import InteractiveMILPProblem
            sage: A = ([1, 1], [3, 1])
            sage: b = (100, 150)
            sage: c = (10, 5)
            sage: P = InteractiveMILPProblem(A, b, c, 
            ....:     variable_type=">=", integer_variables={'x1'})
            sage: p = P.plot()
            sage: p.show()

        In this case the plot works better with the following axes ranges::

            sage: p = P.plot(0, 1000, 0, 1500)
            sage: p.show()

        TESTS:

        We check that zero objective can be dealt with::

            sage: InteractiveMILPProblem(A, b, (0, 0),
            ....: variable_type=">=", integer_variables={'x1'}).plot()
            Graphics object consisting of 57 graphics primitives
        """
        FP = self.plot_feasible_set(*args, **kwds)
        c = self.c().n().change_ring(QQ)
        if c.is_zero():
            return FP
        if 'number_of_cuts' in kwds:
            del kwds['number_of_cuts']
        return self.plot_objective_growth_and_solution(FP, c, *args, **kwds)







class ClusterPicture(SageObject):
    r"""
    Construct a cluster picture, this is a cluster with a specified top 

    INPUT:

    - ``A`` -- a matrix of valuations of differences of roots

    EXAMPLES:

    ::

        sage: R = InteractiveLPProblem(A, b, c, ["C", "B"], problem_type="max",
        ....:     constraint_type=["<=", "<="], variable_type=[">=", ">="])
        sage: P = InteractiveMILPProblem.with_relaxation(R, {'C'})

    """

    def __init__(self, A, parent=None):
        r"""
        See :class:`ClusterPicture` for documentation.

        TESTS::

            sage: C = ClusterPicture()
            sage: TestSuite(C).run()
        """
        self._size = A.dimensions()[0]
        self._top_cluster = Cluster(A)
        self._parent = parent

    @classmethod
    def from_roots(cls, roots):
        return cls(Matrix([[(r1-r2).valuation() for r1 in roots] for r2 in roots]))
    def top_cluster(self):
        return self._top_cluster

    def size(self):
        return self.top_cluster().size()

    def __eq__(self, other):
        r"""
        Check if two Clusters are equal.

        INPUT:

        - ``other`` -- anything

        OUTPUT:

        - ``True`` if ``other`` is an :class:`InteractiveLPProblem` with all details the
          same as ``self``, ``False`` otherwise.

        TESTS::

            sage: from sage_numerical_interactive_mip import InteractiveMILPProblem
            sage: A = ([1, 1], [3, 1])
            sage: b = (1000, 1500)
            sage: c = (10, 5)
            sage: P = InteractiveMILPProblem(A, b, c, variable_type=">=", integer_variables={"x1"})
            sage: P2 = InteractiveMILPProblem(A, b, c, variable_type=">=", integer_variables={"x1"})
            sage: P == P2
            True
            sage: P3 = InteractiveMILPProblem(A, b, c, variable_type=">=")
            sage: P == P3
            False
            sage: R = InteractiveLPProblem(A, b, c, variable_type=">=")
            sage: P4 = InteractiveMILPProblem.with_relaxation(relaxation=R, integer_variables={"x1"})
            sage: P == P4
            True
        """
        return (isinstance(other, InteractiveMILPProblem) and
                self._relaxation == other._relaxation and
                self._integer_variables == other._integer_variables)

    def _latex_(self):
        r"""
        Return a LaTeX representation of ``self``.

        OUTPUT:

        - a string

        TESTS::

            sage: from sage_numerical_interactive_mip import InteractiveMILPProblem
            sage: A = ([1, 1, 2], [3, 1, 7], [6, 4, 5])
            sage: b = (1000, 1500, 2000)
            sage: c = (10, 5, 1)
            sage: P = InteractiveMILPProblem(A, b, c, variable_type=">=", integer_variables={'x1'})
            sage: print(P._latex_())
            \begin{array}{l}
            \begin{array}{lcrcrcrcl}
             \max \mspace{-6mu}&\mspace{-6mu}  \mspace{-6mu}&\mspace{-6mu} 10 x_{1} \mspace{-6mu}&\mspace{-6mu} + \mspace{-6mu}&\mspace{-6mu} 5 x_{2} \mspace{-6mu}&\mspace{-6mu} + \mspace{-6mu}&\mspace{-6mu} x_{3} \mspace{-6mu}&\mspace{-6mu}  \mspace{-6mu}&\mspace{-6mu} \\
             \mspace{-6mu}&\mspace{-6mu}  \mspace{-6mu}&\mspace{-6mu} x_{1} \mspace{-6mu}&\mspace{-6mu} + \mspace{-6mu}&\mspace{-6mu} x_{2} \mspace{-6mu}&\mspace{-6mu} + \mspace{-6mu}&\mspace{-6mu} 2 x_{3} \mspace{-6mu}&\mspace{-6mu} \leq \mspace{-6mu}&\mspace{-6mu} 1000 \\
             \mspace{-6mu}&\mspace{-6mu}  \mspace{-6mu}&\mspace{-6mu} 3 x_{1} \mspace{-6mu}&\mspace{-6mu} + \mspace{-6mu}&\mspace{-6mu} x_{2} \mspace{-6mu}&\mspace{-6mu} + \mspace{-6mu}&\mspace{-6mu} 7 x_{3} \mspace{-6mu}&\mspace{-6mu} \leq \mspace{-6mu}&\mspace{-6mu} 1500 \\
             \mspace{-6mu}&\mspace{-6mu}  \mspace{-6mu}&\mspace{-6mu} 6 x_{1} \mspace{-6mu}&\mspace{-6mu} + \mspace{-6mu}&\mspace{-6mu} 4 x_{2} \mspace{-6mu}&\mspace{-6mu} + \mspace{-6mu}&\mspace{-6mu} 5 x_{3} \mspace{-6mu}&\mspace{-6mu} \leq \mspace{-6mu}&\mspace{-6mu} 2000 \\
            \end{array} \\
            x_{1}, x_{2}, x_{3} \geq 0
             \\x_{1} \in \mathbb{Z} \\x_{2}, x_{3} \in \mathbb{R}\end{array}
        """
        lines = self.relaxation()._latex_()
        integer_var = ""
        continuous_var = ""
        if self.integer_variables():
            integer_var =  r"{} \in {}".format(
                                   ", ".join(map(latex, sorted(self.integer_variables()))),
                                    r"\mathbb{Z}") +  r" \\"
        if self.continuous_variables():
            continuous_var =  r"{} \in {}".format(
                                   ", ".join(map(latex, sorted(self.continuous_variables()))),
                                    r"\mathbb{R}")
        return lines[:-11] + r" \\" + integer_var + continuous_var + lines[-11:]

    def _repr_(self):
        r"""
        Return a string representation of ``self``.

        OUTPUT:

        - a string

        TESTS::

            sage: from sage_numerical_interactive_mip import InteractiveMILPProblem
            sage: A = ([1, 1], [3, 1])
            sage: b = (1000, 1500)
            sage: c = (10, 5)
            sage: P = InteractiveMILPProblem(A, b, c, variable_type=">=", integer_variables={"x1"})
            sage: print(P._repr_())
            MILP problem (use typeset mode to see details)
        """
        return "MILP problem (use typeset mode to see details)"

    def base_ring(self):
        r"""
        Return the base ring of the relaxation of ``self``.

        .. NOTE::

            The base ring of MIClusters is always a field.

        OUTPUT:

        - a ring

        EXAMPLES::

            sage: from sage_numerical_interactive_mip import InteractiveMILPProblem
            sage: A = ([1, 1], [3, 1])
            sage: b = (1000, 1500)
            sage: c = (10, 5)
            sage: P = InteractiveMILPProblem(A, b, c, ["C", "B"], variable_type=">=")
            sage: P.base_ring()
            Rational Field

            sage: c = (10, 5.)
            sage: P = InteractiveMILPProblem(A, b, c, ["C", "B"], variable_type=">=")
            sage: P.base_ring()
            Real Field with 53 bits of precision
        """
        return self.relaxation().base_ring()

        r"""
        Return decision variables of the relaxation of ``self``, i.e. `x`.

        OUTPUT:

        - a vector

        EXAMPLES::

            sage: from sage_numerical_interactive_mip import InteractiveMILPProblem
            sage: A = ([1, 1], [3, 1])
            sage: b = (1000, 1500)
            sage: c = (10, 5)
            sage: P = InteractiveMILPProblem(A, b, c, ["C", "B"], variable_type=">=")
            sage: P.decision_variables()
            (C, B)
            sage: P.x()
            (C, B)
        """
    def is_bounded(self):
        r"""
        Check if ``self`` is bounded.
        """
        raise NotImplementedError("this method is not implemented")

    def plot(self, *args, **kwds):
        r"""
        Return a plot for solving ``self`` graphically.

        INPUT:

        - ``xmin``, ``xmax``, ``ymin``, ``ymax`` -- bounds for the axes, if
          not given, an attempt will be made to pick reasonable values

        - ``alpha`` -- (default: 0.2) determines how opaque are shadows

        OUTPUT:

        - a plot

        .. NOTE::

            This only works for problems with two decision variables.
            On the plot the black arrow indicates the direction of growth
            of the objective. The lines perpendicular to it are level
            curves of the objective. If there are optimal solutions, the
            arrow originates in one of them and the corresponding level
            curve is solid: all points of the feasible set on it are optimal
            solutions. Otherwise the arrow is placed in the center. If the
            problem is infeasible or the objective is zero, a plot of the
            feasible set only is returned.

        EXAMPLES::

            sage: from sage_numerical_interactive_mip import InteractiveMILPProblem
            sage: A = ([1, 1], [3, 1])
            sage: b = (100, 150)
            sage: c = (10, 5)
            sage: P = InteractiveMILPProblem(A, b, c, 
            ....:     variable_type=">=", integer_variables={'x1'})
            sage: p = P.plot()
            sage: p.show()

        In this case the plot works better with the following axes ranges::

            sage: p = P.plot(0, 1000, 0, 1500)
            sage: p.show()

        TESTS:

        We check that zero objective can be dealt with::

            sage: InteractiveMILPProblem(A, b, (0, 0),
            ....: variable_type=">=", integer_variables={'x1'}).plot()
            Graphics object consisting of 57 graphics primitives
        """
        FP = self.plot_feasible_set(*args, **kwds)
        c = self.c().n().change_ring(QQ)
        if c.is_zero():
            return FP
        if 'number_of_cuts' in kwds:
            del kwds['number_of_cuts']
        return self.plot_objective_growth_and_solution(FP, c, *args, **kwds)
