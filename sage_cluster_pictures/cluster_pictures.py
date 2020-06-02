from copy import copy
from collections import defaultdict
from sage.misc.html import HtmlFragment
from sage.rings.all import Infinity, PolynomialRing, QQ, RDF, ZZ
from sage.all import SageObject, Matrix, verbose, ascii_art, unicode_art


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

    def __init__(self, M, parent=None, top=None):
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
        if not top:
            top = self
        self._children = [Cluster(M.matrix_from_rows_and_columns(rs, rs),
                                  parent=self, top=top) for c, rs in children.items()]
        self._top = top

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

    def top_cluster(self):
        r"""
        Return the top cluster for the picture.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: C = Cluster.from_roots([K(1), K(6), K(26), K(126)])
            sage: C.children()[0].children()[0].children()[0].top_cluster().size()
            4

        """
        return self._top

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
        return min(self._M.dense_coefficient_list())

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
        The genus of the cluster, $g$ such that number of roots is $2g+1$ or $2g+2$.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.genus()
            1
            sage: C = Cluster.from_roots([K(1), K(2), K(5), K(10), K(25)])
            sage: C.genus()
            2
            sage: C = Cluster.from_roots([K(1), K(2), K(5), K(10), K(25), K(50)])
            sage: C.genus()
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
            True
            sage: C.children()[1].is_twin()
            False

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
        return (not self.is_ubereven()) and any(c.size() == 2*self.top_cluster().genus() for c in self.children())

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
        return " ".join(("(%s)" if c.is_proper() else "%s") % ascii_art(c) for c in self.children())

    def _unicode_art_(self):
        r"""
        Return a unicode art representation of ``self``.
        """

        if not self.is_proper():
            return "●"
        return " ".join(("(%s)" if c.is_proper() else "%s") % unicode_art(c) for c in self.children())

    # TODO simplify by using relative_depth instead of parent_depth
    def latex_internal(self, prefix="m", prev_obj="first", parent_depth=0):
        latex_string = ""
        child_cnt = 0
        prevprefix = prev_obj
        if not(self.is_proper()):
            return "\\Root[A] {1} {" + prev_obj + "} {" + prefix + "};\n";
        for C in self.children():
            child_cnt += 1
            newprefix = prefix + "c" + str(child_cnt)
            latex_string = latex_string + C.latex_internal(prefix=newprefix, prev_obj=prevprefix, parent_depth=self.depth())
            prevprefix = newprefix
        latex_string = latex_string + "\\ClusterLD " + prefix + "[][" + str(self.depth() - parent_depth) + "] = "
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

            sage: Rp = 7
            sage: K = polygen(Qp(p))
            sage: H = HyperellipticCurve((x-1)*(x-(1+p^2))*(x-(1-p^2))*(x-p)*x*(x-p^3)*(x+p^3))
            sage: Cluster.from_curve(H)
            Cluster with 7 roots and 2 children
        """
        return "Cluster with %s roots and %s children" % (self.size(), self.num_children())

    def is_principal(self):
        r"""
        Check if ``self`` is principal.
        """
        if ((self.is_top_cluster() and self.is_even() and self.num_children() == 2)
            or any(c.size() == 2*self.top_cluster().genus() for c in self.children())):
            return False
        return self.size() >= 3

    def meet(self, other):
        r"""
        Construct `self` $\wedge$ `other`.
        
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
            sage: t1.meet(t2) == a
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
            sage: t1.meet(t2) == a
            True
        """
        if self.is_cotwin():
            return next(c.size() == 2*self.top_cluster().genus()
                    for c in self.children())
        else:
            P = self
            while not P.parent_cluster().is_ubereven() and P.parent_cluster() != P:
                verbose(P)
                P = P.parent_cluster()
            return P



