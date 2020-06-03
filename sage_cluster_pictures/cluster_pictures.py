from copy import copy
from collections import defaultdict
from sage.misc.all import prod
from sage.rings.all import Infinity, PolynomialRing, QQ, RDF, ZZ
from sage.all import SageObject, Matrix, verbose, ascii_art, unicode_art
from sage.graphs.graph import Graph, GenericGraph
import operator


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

    - ``M`` -- a matrix of valuations of differences of roots

    EXAMPLES:

    Example 1.2 from M2D2::

        sage: from sage_cluster_pictures.cluster_pictures import Cluster
        sage: p = 7
        sage: x = polygen(Qp(p))
        sage: H = HyperellipticCurve((x-1)*(x-(1+p^2))*(x-(1-p^2))*(x-p)*x*(x-p^3)*(x+p^3))
        sage: C = Cluster.from_curve(H)
        sage: print(ascii_art(C))
        (((* * *)_2 *)_1 (* * *)_2)_0

    """

    def __init__(self, M, parent=None, top=None, roots=None, depth=None, leading_coefficient=None):
        r"""
        See :class:`Cluster` for documentation.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: C = Cluster(Matrix(ZZ, 4, 4,[\
                       [20, 1, 0, 0 ],\
                       [1, 20, 0, 0 ],\
                       [0, 0, 20, 1 ],\
                       [0, 0, 1, 20 ],\
                    ]))
            sage: C
            Cluster with 4 roots and 2 children

        TESTS::

            sage: #C = Cluster()
            sage: #TestSuite(C).run()
        """
        verbose(M)
        self._M = M
        if depth is not None:
            self._depth = depth
        else:
            self._depth = min(self._M.dense_coefficient_list())
        self._size = M.nrows()
        self._parent_cluster = parent
        self._roots = roots
        self._leading_coefficient = leading_coefficient
        depth = self.depth()
        verbose(depth)
        children = defaultdict(list)
        for r1 in range(self._size):
            if r1 not in sum(children.values(), []):
                for r2 in range(r1, self._size):
                    if M[r1, r2] > depth:
                        children[r1] += [r2]
        verbose(children)
        if not top:
            top = self
        self._children = [Cluster(M.matrix_from_rows_and_columns(rs, rs),
                                  parent=self, top=top,
                                  roots=operator.itemgetter(*rs)(roots)
                                  if roots else None,
                                  leading_coefficient=leading_coefficient)
                                  for c, rs in children.items()]
        self._top = top

    @classmethod
    def from_roots(cls, roots, leading_coefficient=None):
        r"""
        Construct a Cluster from a list of roots.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: Cluster.from_roots([K(1), K(5), K(10)])
            Cluster with 3 roots and 2 children

        """
        K = roots[0].parent()
        return cls(Matrix([[(r1-r2).add_bigoh(K.precision_cap()).valuation()
                            for r1 in roots] for r2 in roots]), roots=roots, leading_coefficient=leading_coefficient)

    @classmethod
    def from_polynomial(cls, f):
        r"""
        Construct a Cluster from a polynomial.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: p = 7
            sage: x = polygen(Qp(p))
            sage: Cluster.from_polynomial((x-1)*(x-(1+p^2))*(x-(1-p^2))*(x-p)*x*(x-p^3)*(x+p^3))
            Cluster with 7 roots and 2 children

        """
        return cls.from_roots(allroots(f), leading_coefficient=f.leading_coefficient())

    @classmethod
    def from_curve(cls, H):
        r"""
        Construct a Cluster from a hyperelliptic curve.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: p = 7
            sage: x = polygen(Qp(p))
            sage: H = HyperellipticCurve((x-1)*(x-(1+p^2))*(x-(1-p^2))*(x-p)*x*(x-p^3)*(x+p^3))
            sage: Cluster.from_curve(H)
            Cluster with 7 roots and 2 children

        """
        if H.hyperelliptic_polynomials()[1] != 0:
            raise ValueError("Curve must be of the form y^2 = f(x)")
        return cls.from_polynomial(H.hyperelliptic_polynomials()[0])

    @classmethod
    def _from_picture_internal(cls, S):
        return
    @classmethod
    def from_picture(cls, S):
        r"""
        Construct a Cluster from an ascii art cluster picture with depths.

        The recommended format is shown in the examples below, however the
        code will ignore all characters except digits brackets and asterisks,
        so extra annotations can be included but will currently be ignored.

        TODO:

        Complete

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: #Cluster.from_picture("((* *)_1 *)_0")
            sage: #Cluster with 3 roots and 2 children


        """
        S = filter(lambda x: x.isdigit() or x in '()*', S)
        verbose(list(S))
        C = cls(Matrix(0,0), depth=0)
        return C

    def parent_cluster(self):
        return self._parent_cluster

    def top_cluster(self):
        r"""
        Return the top cluster for the picture.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(6), K(26), K(126)])
            sage: C.children()[0].children()[0].children()[0].top_cluster().size()
            4

        """
        return self._top

    def leading_coefficient(self):
        r"""
        Return the leading coefficient of the polynomial defining this cluster.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: p = 5
            sage: K = Qp(p)
            sage: x = polygen(K)
            sage: H = HyperellipticCurve(2*(x-1)*(x-(1+p^2))*(x-(1-p^2))*(x-p)*x*(x-p^3)*(x+p^3))
            sage: C = Cluster.from_curve(H)
            sage: C.leading_coefficient()
            2 + O(5^20)

            sage: C = Cluster.from_roots([K(1), K(6), K(26), K(126)])
            sage: C.leading_coefficient()
            Traceback (most recent call last):
            ...
            AttributeError: This cluster does not have a leading coefficient stored.

            sage: C = Cluster(Matrix(ZZ, 4, 4,[\
                       [20, 1, 0, 0 ],\
                       [1, 20, 0, 0 ],\
                       [0, 0, 20, 1 ],\
                       [0, 0, 1, 20 ],\
                    ]))
            sage: C.leading_coefficient()
            Traceback (most recent call last):
            ...
            AttributeError: This cluster does not have a leading coefficient stored.

        """
        if self._leading_coefficient:
            return self._leading_coefficient
        raise AttributeError("This cluster does not have a leading coefficient stored.")

    def roots(self):
        r"""
        Return the list of roots in this cluster.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(6), K(26), K(126)])
            sage: C.roots()
            [1 + O(5^20), 1 + 5 + O(5^20), 1 + 5^2 + O(5^20), 1 + 5^3 + O(5^20)]
            sage: C = Cluster(Matrix(ZZ, 4, 4,[\
                       [20, 1, 0, 0 ],\
                       [1, 20, 0, 0 ],\
                       [0, 0, 20, 1 ],\
                       [0, 0, 1, 20 ],\
                    ]))
            sage: C.roots()
            Traceback (most recent call last):
            ...
            AttributeError: This cluster does not have root information stored.

        """
        if self._roots:
            return self._roots
        raise AttributeError("This cluster does not have root information stored.")

    def depth(self):
        r"""
        Return the depth of the cluster.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.depth()
            0
            sage: C = Cluster.from_roots([K(5), K(25), K(50)])
            sage: C.depth()
            1
            sage: C = Cluster.from_roots([K(1), K(6), K(26), K(126)])
            sage: C.children()[0].children()[0].depth()
            3

        """
        return self._depth

    def relative_depth(self):
        r"""
        Return the depth of the cluster.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.relative_depth()
            0
            sage: C.children()[1].relative_depth()
            1
            sage: C = Cluster.from_roots([K(5), K(25), K(50)])
            sage: C.relative_depth()
            1
            sage: C.children()[1].relative_depth()
            1
            sage: C = Cluster.from_roots([K(1), K(6), K(26), K(126)])
            sage: C.children()[0].children()[0].relative_depth()
            1


        """
        if self.is_top_cluster():
            return self.depth()
        return self.depth() - self.parent_cluster().depth()

    def size(self):
        return self._size

    def genus(self):
        r"""
        The genus of the cluster, $g$ such that number of odd children is $2g+1$ or $2g+2$.

        TODO:

        Check these examples actually make sense.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.genus()
            0
            sage: C = Cluster.from_roots([K(1), K(2), K(5), K(10), K(25)])
            sage: C.genus()
            1
            sage: C = Cluster.from_roots([K(1), K(2), K(5), K(10), K(25), K(50)])
            sage: C.genus()
            0

        """
        return (len([0 for c in self.children() if c.is_odd()]) - 1)//2

    def curve_genus(self):
        r"""
        The genus of the curve on the generic fibre, $g$ such that number of roots is $2g+1$ or $2g+2$.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.curve_genus()
            1
            sage: C = Cluster.from_roots([K(1), K(2), K(5), K(10), K(25)])
            sage: C.curve_genus()
            2
            sage: C = Cluster.from_roots([K(1), K(2), K(5), K(10), K(25), K(50)])
            sage: C.curve_genus()
            2

        """
        return (self.size() - 1)//2

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

    def is_top_cluster(self):
        r"""
        Check if the Cluster is the top cluster for the picture.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.is_top_cluster()
            True
            sage: C.children()[0].is_top_cluster()
            False

        """
        return (not self.parent_cluster())

    def is_twin(self):
        r"""
        Check if the Cluster is a twin.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.is_twin()
            False
            sage: C.children()[0].is_twin()
            False
            sage: C.children()[1].is_twin()
            True

        """
        return self.size() == 2

    def is_cotwin(self):
        r"""
        Check if the Cluster is a cotwin.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.is_cotwin()
            True
            sage: C.children()[0].is_cotwin()
            False
            sage: C.children()[1].is_cotwin()
            False
            sage: C = Cluster.from_roots([K(1), K(5), K(10), K(35)])
            sage: C.is_cotwin()
            False
            sage: C.children()[0].is_cotwin()
            False
            sage: C.children()[1].is_cotwin()
            True
            sage: C = Cluster.from_roots([K(1), K(2), K(10), K(35)])
            sage: C.is_cotwin()
            True
            sage: C.children()[0].is_cotwin()
            False
            sage: C.children()[1].is_cotwin()
            False

        """
        return (not self.is_ubereven()) and any(c.size() == 2*self.top_cluster().curve_genus() for c in self.children())

    def is_proper(self):
        r"""

        Returns whether or not `self` is proper, i.e. has size at least 2.
        
        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.is_proper()
            True
            sage: C.children()[1].is_proper()
            True
            sage: C.children()[0].is_proper()
            False
        """
        return self.size() > 1

    def children(self):
        r"""

        Returns all children of `self`.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.children()
            [Cluster with 1 roots and 0 children, Cluster with 2 roots and 2 children]

        """
        return self._children

    #def add_child(self, C):
    #    C._parent = self
    #    self._children.append(C)
    #    self._size += C.size()

    def all_descendents(self):
        r"""

        Return (an iterator over) all descendent clusters of `self` (including `self`).

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10), K(35), K(135)])
            sage: list(C.all_descendents())
            [Cluster with 5 roots and 2 children,
             Cluster with 1 roots and 0 children,
             Cluster with 4 roots and 2 children,
             Cluster with 1 roots and 0 children,
             Cluster with 3 roots and 2 children]
        """
        yield self
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

    #def __eq__(self, other):
    #    r"""
    #    Check if two Clusters are equal.

    #    INPUT:

    #    - ``other`` -- anything

    #    OUTPUT:

    #    - ``True`` if ``other`` is the same cluster as ``self``, 
    #        `False`` otherwise.

    #    """
    #    return False
    #return (isinstance(other, InteractiveMILPProblem) and
    #        self._relaxation == other._relaxation and
    #        self._integer_variables == other._integer_variables)

    def _ascii_art_(self):
        r"""
        Return an ascii art representation of ``self``.
        """

        if not self.is_proper():
            return "*"
        return "(" + " ".join(("%s" if c.is_proper() else "%s") % ascii_art(c) for c in self.children()) + ")_%s" % self.relative_depth()

    def _unicode_art_(self):
        r"""
        Return a unicode art representation of ``self``.
        """

        if not self.is_proper():
            return "●"
        return "(" + " ".join(("%s" if c.is_proper() else "%s") % unicode_art(c) for c in self.children()) + ")_%s" % self.relative_depth()

    # TODO simplify by using relative_depth instead of parent_depth
    def latex_internal(self, prefix="m", prev_obj="first"):
        latex_string = ""
        child_cnt = 0
        prevprefix = prev_obj
        if not(self.is_proper()):
            return "\\Root[A] {1} {" + prev_obj + "} {" + prefix + "};\n";
        for C in self.children():
            child_cnt += 1
            newprefix = prefix + "c" + str(child_cnt)
            latex_string = latex_string + C.latex_internal(prefix=newprefix, prev_obj=prevprefix)
            prevprefix = newprefix
        latex_string = latex_string + "\\ClusterLD " + prefix + "[][" + str(self.relative_depth()) + "] = "
        for i in range(1, child_cnt+1):
            latex_string = latex_string + "(" + prefix + "c" + str(i) + ")"
        latex_string = latex_string + ";\n"
        return latex_string

    def _latex_(self):
        r"""
        Return a LaTeX representation of ``self``.

        OUTPUT:

        - a string

        """
        return r" \def\cdepthscale{0.5}   \clusterpicture" + \
             self.latex_internal() + r"\endclusterpicture"

    def _repr_(self):
        r"""
        Return a string representation of ``self``.

        OUTPUT:

        - a string

        TESTS::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: p = 7
            sage: x = polygen(Qp(p))
            sage: H = HyperellipticCurve((x-1)*(x-(1+p^2))*(x-(1-p^2))*(x-p)*x*(x-p^3)*(x+p^3))
            sage: Cluster.from_curve(H)
            Cluster with 7 roots and 2 children
        """
        return "Cluster with %s roots and %s children" % (self.size(), len(self.children()))

    def is_principal(self):
        r"""
        Check if ``self`` is principal.
        """
        if ((self.is_top_cluster() and self.is_even() and len(self.children()) == 2)
            or any(c.size() == 2*self.top_cluster().curve_genus() for c in self.children())):
            return False
        return self.size() >= 3

    def meet(self, other):
        r"""
        Construct `self` $\\wedge$ `other`.
        
        EXAMPLES:

        Example 3.6 from the users guide::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(7,150)
            sage: x = polygen(K)
            sage: L = K.extension(x^2 + 1, names='a')
            sage: x = polygen(L)
            sage: L2 = L.extension(x^2 - 7, names='b')
            sage: x = polygen(L2)
            sage: H = HyperellipticCurve((x^2+7^2)*(x^2-7^(15))*(x-7^6)*(x-7^6-7^9))
            sage: R = Cluster.from_curve(H)
            sage: a = R.children()[0]
            sage: t1 = a.children()[0]
            sage: t2 = a.children()[1]
            sage: t1.meet(t2) == a
            True
            sage: t1.meet(a) == a
            True
            sage: t1.meet(R.children()[1]) == R
            True
        """
        Ps, Po = self, other
        while Ps != Po:
            verbose(Ps)
            verbose(Po)
            if Ps.size() < Po.size():
                Ps = Ps.parent_cluster()
            else:
                Po = Po.parent_cluster()
        return Ps


    def star(self):
        r"""
        Construct `self*`, if `self` is not a cotwin this is the
        smallest cluster containing `self` whose parent is not übereven (and
        the top cluster if no such cluster exists). If `self` is a cotwin,
        its star is its child of size `2g`.
        
        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(7,150)
            sage: x = polygen(K)
            sage: L = K.extension(x^2 + 1, names='a')
            sage: x = polygen(L)
            sage: L2 = L.extension(x^2 - 7, names='b')
            sage: x = polygen(L2)
            sage: H = HyperellipticCurve((x^2+7^2)*(x^2-7^(15))*(x-7^6)*(x-7^6-7^9))
            sage: R = Cluster.from_curve(H)
            sage: a = R.children()[0]
            sage: t1 = a.children()[0]
            sage: t2 = a.children()[1]
            sage: t1.star() == a
            True
            sage: t2.star() == a
            True
            sage: a.star() == a
            True
            sage: R.star() == a
            True

        Some cotwins::

            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.star()
            Cluster with 2 roots and 2 children

            sage: C = Cluster.from_roots([K(1), K(2), K(10), K(35)])
            sage: C.star()
            Cluster with 2 roots and 2 children

            sage: C = Cluster.from_roots([K(1), K(5), K(10), K(35)])
            sage: C.children()[1].star()
            Cluster with 2 roots and 2 children

        """
        if self.is_cotwin():
            verbose(self)
            verbose(list(c for c in self.children()
                if c.size() == 2*self.top_cluster().curve_genus()))
            return next(c for c in self.children()
                if c.size() == 2*self.top_cluster().curve_genus())
        else:
            P = self
            while P.parent_cluster() and P.parent_cluster().is_ubereven():
                verbose(P)
                P = P.parent_cluster()
            return P


    def is_center(self, z):
        r"""
        Checks if a point `z` is a center of the cluster, i.e.
        $$\\min_{r\\in self}v(z-r) = self.depth()$$
        """
        return min((z-r).valuation() for r in self.roots()) == self.depth()

    def center(self):
        r"""
        A choice of center of `self`, i.e. some $z_{\\mathfrak{s}} \\in K^{\\mathrm{sep}}$ with $\\min _{r \\in \\mathfrak{s}} v\\left(z_{\\mathfrak{s}}-r\\right)=d_{\\mathfrak{s}}$.
        
        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster(Matrix(ZZ, 4, 4,[\
                       [20, 1, 0, 0 ],\
                       [1, 20, 0, 0 ],\
                       [0, 0, 20, 1 ],\
                       [0, 0, 1, 20 ],\
                    ]))
            sage: C.roots()
            Traceback (most recent call last):
            ...
            AttributeError: This cluster does not have root information stored.
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.center()
            1 + O(5^20)
            sage: C.is_center(C.center())
            True

            sage: C = Cluster.from_roots([K(1), K(2), K(10), K(35)])
            sage: C.center()
            1 + O(5^20)
            sage: C.is_center(C.center())
            True

        """
        return self.roots()[0]

    # TODO
    def theta(self):
        r"""
        A choice $\\sqrt{c \\prod_{r \\notin \\mathfrak{s}}\\left(z_{\\mathfrak{s}}-r\\right)}.
        
        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: p = 5
            sage: K = Qp(p)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.theta()
            Traceback (most recent call last):
            ...
            AttributeError: This cluster does not have a leading coefficient stored.
            sage: x = polygen(K)
            sage: C = Cluster.from_polynomial((x-1)*(x-(1+p^2))*(x-(1-p^2))*(x-p)*x*(x-p^3)*(x+p^3))
            sage: C.theta()
            1 + O(5^20)
            sage: D = C.children()[0]
            sage: D.theta()
            2 + 5 + 2*5^2 + 5^3 + 2*5^4 + 5^5 + 4*5^6 + 2*5^7 + 2*5^8 + 2*5^9 + 5^10 + 4*5^11 + 2*5^13 + 3*5^14 + 4*5^15 + O(5^16)

        """
        P = self.leading_coefficient()*prod(self.center() - r for r in self.top_cluster().roots() if r not in self.roots())
        return P.sqrt()

    # TODO
    def epsilon(self, sigma):
        r"""
        .. MATH::

            \frac{\sigma\left(\theta_{s^{*}}\right)}{\theta_{\left(\sigma_{\mathfrak{s}}\right)^{*}}} \bmod \mathfrak{m} \in\{\pm 1\} \text { if } \mathfrak{s} \text { even or cotwin, } \epsilon_{\mathfrak{s}}(\sigma)=0 \text { otherwise }

        INPUT:

        - `sigma` an element of Galois (a function $K \\to K$), which can act on `self` and the field.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)], leading_coefficient=1)
            sage: C.epsilon(lambda x: x)
            1 + O(5^20)
            sage: C = Cluster.from_roots([K(1), K(2), K(10), K(35)], leading_coefficient=1)
            sage: C.children()[0].epsilon(lambda x: x)
            0

        """
        if self.is_even() or self.is_cotwin():
            return sigma(self.star().theta())\
                 / sigma(self).star().theta()
        return 0
    
    def BY_tree(self, check=True):
        r"""

        Contstructs the BY-tree associated to the cluster picture.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(7,150)
            sage: x = polygen(K)
            sage: L = K.extension(x^2 + 1, names='a')
            sage: x = polygen(L)
            sage: L2 = L.extension(x^2 - 7, names='b')
            sage: x = polygen(L2)
            sage: H = HyperellipticCurve((x^2+7^2)*(x^2-7^(15))*(x-7^6)*(x-7^6-7^9))
            sage: R = Cluster.from_curve(H)
            sage: R.BY_tree()
            BY-tree with 1 yellow vertices, 3 blue vertices, 3 yellow edges, 0, blue edges

        """
        T = BYTree()
        for s in self.all_descendents():
            verbose(s)
            if s.is_proper():
                if s.is_ubereven():
                    T.add_yellow_vertex(s)
                else:
                    T.add_blue_vertex(s)
                if s.parent_cluster():
                    if s.is_even():
                        T.add_yellow_edge((s, s.parent_cluster(), 2*s.relative_depth()))
                    else:
                        T.add_blue_edge((s, s.parent_cluster(), s.relative_depth()))

        return T

    def __hash__(self):
        return hash(id(self))

    def __eq__(self, other):
        return self is other

    def __ne__(self, other):
        return self is not other

    def __lt__(self, other):
        return id(self) < id(other)


class BYTree(Graph):
    r"""
    Construct a BY-tree.

    EXAMPLES:


    """

    def __init__(self, *args, **kwargs):
        r"""
        See :class:`BYTree` for documentation.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T
            BY-tree with 0 yellow vertices, 0 blue vertices, 0 yellow edges, 0, blue edges

        TESTS::

            sage: #C = BYTree()
            sage: #TestSuite(C).run()
        """
        kwargs['weighted'] = True
        super(BYTree, self).__init__(*args, **kwargs)
        self._blue_vertices = []
        self._yellow_vertices = []
        self._blue_edges = []
        self._yellow_edges = []
        self._genera = dict()

    def genus(self, vertex):
        r"""
        Returns the genus of a vertex.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 0)
            sage: T.genus('v1')
            0
            sage: T.add_blue_vertex('v2', 1)
            sage: T.genus('v2')
            1
            sage: T.add_yellow_vertex('v3')
            sage: T.genus('v3')
            0

        """
        return self._genera[vertex]

    # TODO potentially override default add_edge and add_vertex and use super below to prevent people screwing up the BY tree

    def add_blue_vertex(self, label, genus=0):
        r"""

        Adds a blue vertex to the BY-tree.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 0)
            sage: T
            BY-tree with 0 yellow vertices, 1 blue vertices, 0 yellow edges, 0, blue edges
            sage: T.add_blue_vertex('v2', 1)
            sage: T
            BY-tree with 0 yellow vertices, 2 blue vertices, 0 yellow edges, 0, blue edges
            sage: T.add_blue_vertex('v3')
            sage: T.genus('v3')
            0

        """
        self.add_vertex(label)
        self._genera[label] = genus
        self._blue_vertices.append(label)

    def add_yellow_vertex(self, label):
        r"""

        Adds a yellow vertex to the BY-tree.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_yellow_vertex('v1')
            sage: T
            BY-tree with 1 yellow vertices, 0 blue vertices, 0 yellow edges, 0, blue edges
            sage: T.add_yellow_vertex('v2')
            sage: T
            BY-tree with 2 yellow vertices, 0 blue vertices, 0 yellow edges, 0, blue edges

        """
        self.add_vertex(label)
        self._genera[label] = 0
        self._yellow_vertices.append(label)

    def blue_vertices(self):
        r"""

        Returns the list of blue vertices of `self`.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 0)
            sage: T.add_blue_vertex('v2', 1)
            sage: T.add_yellow_vertex('v3')
            sage: T.blue_vertices()
            ['v1', 'v2']

        """
        return self._blue_vertices

    def yellow_vertices(self):
        r"""

        Returns the list of yellow vertices of `self`.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 0)
            sage: T.add_yellow_vertex('v3')
            sage: T.add_blue_vertex('v2', 1)
            sage: T.add_yellow_vertex('v4')
            sage: T.yellow_vertices()
            ['v3', 'v4']
        
        """

        return self._yellow_vertices

    def add_blue_edge(self, a):
        r"""

        Adds a blue edge to the BY-tree.

        INPUT:

        - `a` - triple of vertices and a weight.


        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 2)
            sage: T.add_yellow_vertex('v3')
            sage: T.add_yellow_vertex('v4')
            sage: T.add_yellow_edge(('v4', 'v1', 1))
            sage: T.add_yellow_edge(('v4', 'v2', 1))
            sage: T.add_blue_edge(('v3', 'v4', 2))
            sage: T
            BY-tree with 2 yellow vertices, 2 blue vertices, 2 yellow edges, 1, blue edges

        """

        self.add_edge(a)
        e = next(ee for ee in self.edges_incident(a[0]) if ee[0] == a[1] or ee[1] == a[1])
        verbose(e)
        self._blue_edges.append(e)

    def add_yellow_edge(self, a):
        r"""

        Adds a yellow edge to the BY-tree.

        INPUT:

        - `a` - triple of vertices and a weight.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 2)
            sage: T.add_yellow_vertex('v3')
            sage: T.add_yellow_vertex('v4')
            sage: T.add_yellow_edge(('v4', 'v1', 1))
            sage: T.add_yellow_edge(('v4', 'v2', 1))
            sage: T.add_blue_edge(('v3', 'v4', 2))
            sage: T
            BY-tree with 2 yellow vertices, 2 blue vertices, 2 yellow edges, 1, blue edges

        """
        self.add_edge(a)
        e = next(ee for ee in self.edges_incident(a[0]) if ee[0] == a[1] or ee[1] == a[1])
        verbose(e)
        self._yellow_edges.append(e)

    def blue_edges(self):
        r"""

        Returns the list of yellow vertices of `self`.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 2)
            sage: T.add_yellow_vertex('v3')
            sage: T.add_yellow_vertex('v4')
            sage: T.add_yellow_edge(('v4', 'v1', 1))
            sage: T.add_yellow_edge(('v4', 'v2', 1))
            sage: T.add_blue_edge(('v3', 'v4', 2))
            sage: T.blue_edges()
            [('v3', 'v4', 2)]

        """
        return self._blue_edges

    def yellow_edges(self):
        r"""

        Returns the list of yellow edges of `self`.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 2)
            sage: T.add_yellow_vertex('v3')
            sage: T.add_yellow_vertex('v4')
            sage: T.add_yellow_edge(('v4', 'v1', 1))
            sage: T.add_yellow_edge(('v4', 'v2', 1))
            sage: T.add_blue_edge(('v3', 'v4', 2))
            sage: T.yellow_edges()
            [('v1', 'v4', 1), ('v2', 'v4', 1)]
        
        """
        return self._yellow_edges


    def _repr_(self):
        r"""

        Returns a string representation of `self`.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 2)
            sage: T.add_yellow_vertex('v3')
            sage: T.add_yellow_vertex('v4')
            sage: T.add_yellow_edge(('v4', 'v1', 1))
            sage: T.add_yellow_edge(('v4', 'v2', 1))
            sage: T.add_blue_edge(('v3', 'v4', 2))
            sage: T
            BY-tree with 2 yellow vertices, 2 blue vertices, 2 yellow edges, 1, blue edges

        """
        return "BY-tree with %s yellow vertices, %s blue vertices, %s yellow edges, %s, blue edges" % (len(self.yellow_vertices()), len(self.blue_vertices()), len(self.yellow_edges()), len(self.blue_edges()))

    def validate(self):
        r"""

        Checks if `self` is a valid BY-tree, i.e. it is a tree, all vertices / edges are coloured blue or yellow, all edges have a positive weight, all vertices have nonnegative genus, and:
        (1) yellow vertices have genus 0, degree $\\ge 3$, and only yellow edges;
        (2) blue vertices of genus 0 have at least one yellow edge;
        (3) at every vertex, $2g(v) + 2 \\ge #$ blue edges at $v$.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 2)
            sage: T.add_yellow_vertex('v3')
            sage: T.add_yellow_vertex('v4')
            sage: T.add_yellow_edge(('v4', 'v1', 1))
            sage: T.add_yellow_edge(('v4', 'v2', 1))
            sage: T.add_blue_edge(('v3', 'v4', 2))
            sage: T.validate()
            False

        User guide section 10, example 1.2 ::

            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 0)
            sage: T.add_yellow_edge(('v1', 'v2', 2))
            sage: T.validate()
            True


        User guide section 10, example 1.3 ::

            sage: T = BYTree()
            sage: T.add_blue_vertex('v1')
            sage: T.add_blue_vertex('v2')
            sage: T.add_blue_vertex('v3')
            sage: T.add_yellow_vertex('v4')
            sage: T.add_blue_vertex('v5')
            sage: T.add_blue_vertex('v6')
            sage: T.add_blue_vertex('v7')
            sage: T.add_blue_vertex('v8')
            sage: T.add_yellow_edge(('v1', 'v4', 2))
            sage: T.add_yellow_edge(('v2', 'v4', 2))
            sage: T.add_yellow_edge(('v6', 'v4', 2))
            sage: T.add_yellow_edge(('v7', 'v4', 2))
            sage: T.add_blue_edge(('v7', 'v5', 2))
            sage: T.add_yellow_edge(('v3', 'v5', 2))
            sage: T.add_yellow_edge(('v8', 'v5', 2))
            sage: T.validate()
            True

        """

        if not self.is_tree():
            verbose("not a tree")
            return False
        if self.has_multiple_edges():
            verbose("has multiple edges")
            return False
        if self.has_loops():
            verbose("not a tree")
            return False

        # TODO these checks aren't as good as they could be, but hopefully good enough
        if len(self.blue_vertices()) + len(self.yellow_vertices())\
                != len(self.vertices()):
            verbose("vertices not bicoloured")
            return False

        # TODO these checks aren't as good as they could be, but hopefully good enough
        if len(self.blue_edges()) + len(self.yellow_edges())\
                != len(self.edges(sort=False)):
            verbose("edges not bicoloured")
            return False
        if not all(self.genus(v) >= 0 for v in self.vertices()):
            verbose("genus function negatively valued")
            return False

        if not all(self.genus(y) == 0 for y in self.yellow_vertices()):
            verbose("yellow vertex of positive genus")
            return False

        if not all(self.degree(y) >= 3 for y in self.yellow_vertices()):
            verbose("yellow vertex of degree less than 3")
            return False
        if not all(all(e in self.yellow_edges() for e in self.edges_incident(y))
                   for y in self.yellow_vertices()):
            verbose("yellow vertex with non-yellow edge")
            return False

        if not all(any(y in self.yellow_edges()
                       for y in self.edges_incident(v))
                   for v in self.blue_vertices() if self.genus(v) == 0):
            verbose("blue genus zero vertex with yellow edge")
            return False
        if not all(2*self.genus(v) + 2 >=
                   len([e for e in self.edges_incident(v)
                       if e in self.blue_edges()])
                   for v in self.vertices()):
            verbose("2g+2 less than number of blue edges leaving a vertex")
            return False

        return True

    def graphplot(self, **options):
        from sage.graphs.graph_plot import GraphPlot
        options['vertex_colors'] = {'lightskyblue': self.blue_vertices(),
                                    'khaki': self.yellow_vertices()}
        options['edge_colors'] = {'lightskyblue': self.blue_edges(),
                                  'khaki': self.yellow_edges()}
        if 'edge_thickness' not in options:
            options['edge_thickness'] = 3
        if 'vertex_labels' not in options:
            options['vertex_labels'] = False
        # options['layout'] = 'graphviz'
        # options['prog'] = 'neato'
        if 'edge_labels' not in options:
            options['edge_labels'] = True
        verbose(options)
        return super().graphplot(**options)

