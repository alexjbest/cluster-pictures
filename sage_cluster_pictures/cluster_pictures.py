from copy import copy
from collections import defaultdict
from sage.misc.all import prod
from sage.rings.all import Infinity, PolynomialRing, QQ, RDF, ZZ, Zmod, Qq
from sage.all import SageObject, Matrix, verbose, ascii_art, unicode_art, cyclotomic_polynomial, gcd, CombinatorialFreeModule, Integer
from sage.graphs.graph import Graph, GenericGraph
from sage.combinat.all import Combinations
from functools import reduce
from sage.dynamics.finite_dynamical_system import FiniteDynamicalSystem
from sage.functions.min_max import min_symbolic
from sage.calculus.functional import simplify


def our_extension(p,e,f, prec=150):
    F2 = Qq(p**f, prec=prec, names='b')
    rho = F2.frobenius_endomorphism()
    if e == 1:
        F3 = F2
        phi = F3.Hom(F3).identity()
    else:
        R = PolynomialRing(F2, names='x')
        pol = R(cyclotomic_polynomial(e))
        zeta = pol.roots()[0][0]
        F3 = F2.extension(R.gens()[0]**e - p, names='a')
        phi = F3.hom([F3.gens()[0]*zeta], F3)
        rho = F3.hom([F3.gens()[0]], base_map=rho)
    return F3, phi, rho

def allroots(pol):
    p = pol.base_ring().prime()
    assert(pol.base_ring().absolute_degree() == 1)
    for n in range(2,100):
        for e in range(1,n):
            f = n-e
            if (Zmod(e)(p)**f != 1) or (Zmod(p)(e) == 0):
                continue
            F, phi, rho = our_extension(p, e, f)
            polF = pol.change_ring(F)
            roots = polF.roots()
            if sum(d for _, d in roots) == pol.degree():
                roots = sum([d*[r] for r, d in roots], [])
                return roots, phi, rho

#def allroots(f):
#    while True:
#        roots = f.roots()
#        if sum(d for _, d in roots) == f.degree():
#            return sum([d*[r] for r, d in roots], [])
#        _, g = min([(g.degree(), g) for g, d in f.factor() if g.degree() > 1])
#        K = g.root_field('a')
#        f = f.change_ring(K)
#    return roots

def teichmuller_trunc(x, n):
    K = x.parent()
    return K.uniformiser_pow(x.valuation())*sum(a*K.uniformiser_pow(i) for i, a in enumerate(x.teichmuller_expansion()[0:(n*K.absolute_e())]))

def find_root_difference_valuations(f, g):
    R = f.parent()
    assert g in R
    S = PolynomialRing(R, names='t')
    t = S.gens()[0]
    h = f.subs(t-R.gens()[0]).resultant(g.subs(t)).shift(-g.gcd(f).degree())
    newt_slopes = h.newton_slopes()
    return [newt_slopes[g.degree()*i] for i in range(ZZ(len(newt_slopes)/g.degree()))]


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
        ((* * *)_2 (* (* * *)_2)_1)_0

    TODO:

    See if fake `p`-adic extensions can do anything for us, https://mclf.readthedocs.io/en/latest/padic_extensions.html , or Julian's semistable reduction graphs.

    """

    def __init__(self, M=[], parent=None, top=None, roots=None, depth=None, leading_coefficient=None):
        r"""
        See :class:`Cluster` for documentation.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: C = Cluster([\
                       [20, 2, 0],\
                       [2, 20, 0],\
                       [0, 0, 20],\
                    ])
            sage: C
            Cluster with 3 roots and 2 children

            sage: C = Cluster(Matrix(ZZ, 4, 4,[\
                       [20, 1, 0, 0 ],\
                       [1, 20, 0, 0 ],\
                       [0, 0, 20, 1 ],\
                       [0, 0, 1, 20 ],\
                    ]))
            sage: C
            Cluster with 4 roots and 2 children
            sage: #TestSuite(C).run()
        """
        # TODO check somewhere that the prime 2 isn't used!
        verbose(M)
        verbose(roots)
        self._M = M
        self._size = len(list(M))
        if depth is not None:
            self._depth = depth
        else:
            if self._size:
                self._depth = simplify(reduce(min_symbolic, (self._M[r1][r2]
                                     for r1 in range(self._size)
                                     for r2 in range(self._size))))
        self._parent_cluster = parent
        self._roots = roots
        self._leading_coefficient = leading_coefficient
        children = defaultdict(list)
        for r1 in range(self._size):
            if r1 not in sum(children.values(), []):
                if not self._size == 1:
                    children[r1] = [r1]
                for r2 in range(r1 + 1, self._size):
                    if M[r1][r2] > self._depth:
                        children[r1] += [r2]
        verbose(children)
        if not top:
            top = self
        self._children = [Cluster([[M[r1][r2]
                          for r1 in range(self._size) if r1 in rs]
                          for r2 in range(self._size) if r2 in rs],
                          parent=self, top=top,
                          roots=[r for i, r in enumerate(roots) if i in rs]
                                if roots else None,
                          leading_coefficient=leading_coefficient)
                          for c, rs in children.items()]
        self._children.sort()
        self._top = top

    # TODO set _frobenius from from_roots
    @classmethod
    def from_roots(cls, roots, leading_coefficient=None, phi=None, rho=None):
        r"""
        Construct a Cluster from a list of roots.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: Cluster.from_roots([K(1), K(5), K(10)])
            Cluster with 3 roots and 2 children

        """
        assert all(r1.parent() == r2.parent() for r1 in roots for r2 in roots)
        K = roots[0].parent()
        verbose(K)
        e = K.absolute_e()
        cluster = cls(Matrix([[(r1-r2).add_bigoh(K.precision_cap()).valuation()/e
                              for r1 in roots] for r2 in roots]), roots=roots,
                      leading_coefficient=leading_coefficient)
        verbose(cluster.roots())
        if phi:
            # Put inertia action
            cluster.put_inertia_action(phi)
            cluster._inertia_K = phi
        if rho:
            # Put Frobenius action
            cluster.put_frobenius_action(rho)
            cluster._frobenius_K = rho
        return cluster

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
        roots, phi, rho = allroots(f)
        return cls.from_roots(roots, leading_coefficient=f.leading_coefficient(), phi=phi, rho=rho)

    @classmethod
    def from_polynomial_without_roots(cls, f, infinity=10**5, factors=None):
        r"""
        Construct a Cluster from a polynomial without computing its root.
        This has the advantage that it also works for wild extensions, but you lose the root data.

        NOTE:

        The following input is currently broken

            x = polygen(Zp(3))
            F = (3 + 3^2 + 3^3 + 2*3^4 + 3^5 + 3^6 + 3^9 + 3^10 + 2*3^11 + 2*3^12 + 2*3^13 + 2*3^14 + 3^16 + 3^17 + 2*3^18 + O(3^21))*x^3 + (2*3^2 + 3^3 + 3^4 + 2*3^6 + 2*3^8 + 2*3^9 + 3^10 + 3^11 + 3^13 + 3^14 + 2*3^16 + 3^17 + 2*3^18 + O(3^22))*x^2 + (3 + 3^2 + 3^3 + 2*3^4 + 3^5 + 3^6 + 3^7 + 3^10 + 3^12 + 2*3^15 + 2*3^16 + 2*3^18 + 3^19 + 3^20 + O(3^21))*x + 3 + 3^2 + 3^3 + 3^4 + 3^5 + 2*3^6 + 2*3^7 + 3^8 + 2*3^11 + 3^12 + 3^13 + 3^14 + 3^15 + 3^17 + 2*3^18 + 3^19 + O(3^21)
            Cluster.from_polynomial_without_roots(F)

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: p = 23
            sage: x = polygen(Qp(p,200))
            sage: f = x*(x-p^2)*(x-p)*(x-p-p^3)*(x-1)*(x-1-p^4)*(x-p-1)*(x-p-1-p^5)
            sage: Cluster.from_polynomial_without_roots(f)._ascii_art_()
            '(((* *)_1 (* *)_2)_1 ((* *)_3 (* *)_4)_1)_0'

        """

        if factors == None:
            assert f.is_squarefree()
            factors = f.factor()
        factors.sort()
        clusters_list = []
        for g in factors:
            Lg = []
            for h in factors:
                Lh = find_root_difference_valuations(h[0], g[0])
                assert len(Lh) == 0 or infinity > Lh[0] # infinity must be greater than all valuations of differences
                if g == h:
                    Lh = [infinity] + Lh
                Lg.append(Lh)
            verbose(Lg)
            verbose(g[0].degree())
            for i in range(g[0].degree()):
                clusters_list.append([sum(Lg,[]), Lg, Cluster([[ infinity ]])])
        for s in clusters_list:
            s[0].sort(reverse=True)
            s[0][0] = s[0][1]
            for L in s[1]:
                if L.count(infinity) > 0:
                    L[0] = s[0][0]

        verbose(clusters_list)
        while len(clusters_list) > 1:
            clusters_list.sort(reverse=True)
            x = clusters_list[0]
            verbose('processing')
            verbose(x)
            dist_list = x[0]
            dist_per_orbit = x[1]
            d = dist_list[0]
            n = dist_list.count(d)
            children = [x[2]]
            number_to_remove = n - x[2].size()
            clusters_list.remove(x)
            while number_to_remove > 0:
                y = clusters_list[0]
                assert(y[0] == dist_list)
                assert(y[1] == dist_per_orbit)
                children.append(y[2])
                number_to_remove -= y[2].size()
                verbose('removed')
                verbose(y)
                clusters_list.remove(y)
            assert number_to_remove == 0 # TODO check
            new_cluster = Cluster([], depth=d)
            new_cluster._children = children
            for s in children:
                s._parent_cluster = new_cluster
                new_cluster._size += s.size()
            new_cluster._children.sort()
            if n == len(dist_list):
                new_d = dist_list[n-1]
            else:
                new_d = dist_list[n]
            new_dist_list = [min(z, new_d) for z in dist_list]
            new_dist_per_orbit = [[min(z, new_d) for z in L ] for L in dist_per_orbit]

            clusters_list.append([new_dist_list, new_dist_per_orbit, new_cluster])
            verbose('added')
            verbose(clusters_list[len(clusters_list)-1])

        final_cluster = clusters_list[0][2]
        assert final_cluster.size() == f.degree()
        return final_cluster

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
    def from_picture(cls, S):
        r"""
        Construct a Cluster from an ascii art cluster picture with depths.

        The recommended format is shown in the examples below, however the
        code will ignore all characters except digits brackets and asterisks,
        so extra annotations can be included but will currently be ignored.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: Cluster.from_picture("((* *)_1 *)_0")
            Cluster with 3 roots and 2 children

        A slighly more complicated example::

            sage: x = polygen(Qp(3))
            sage: F = (1 + 2*3 + 2*3^2 + 2*3^3 + 3^4 + 2*3^6 + 2*3^7 + 3^8 + 2*3^9 + 3^11 + 3^12 + 3^15 + 2*3^16 + 2*3^19 + O(3^20))*x^6 + (2 + 3 + 2*3^2 + 3^3 + 2*3^4 + 2*3^5 + 3^6 + 2*3^8 + 3^9 + 2*3^10 + 2*3^11 + 3^12 + 3^13 + 3^15 + 3^16 + 2*3^17 + 2*3^19 + O(3^20))*x^5 + (3 + 2*3^2 + 2*3^3 + 2*3^4 + 3^6 + 3^7 + 3^10 + 3^12 + 2*3^13 + 2*3^14 + 3^15 + 3^16 + 2*3^17 + 3^18 + 3^19 + 3^20 + O(3^21))*x^4 + (3^3 + 2*3^4 + 3^6 + 2*3^10 + 2*3^11 + 3^12 + 3^13 + 3^14 + 2*3^15 + 2*3^16 + 3^18 + 3^19 + 2*3^20 + 2*3^21 + 2*3^22 + O(3^23))*x^3 + (2 + 3 + 3^2 + 2*3^3 + 3^4 + 2*3^7 + 3^9 + 3^11 + 3^12 + 3^13 + 2*3^14 + 2*3^15 + 3^16 + 2*3^17 + 2*3^18 + 2*3^19 + O(3^20))*x^2 + (3 + 2*3^2 + 3^3 + 3^4 + 3^5 + 2*3^6 + 2*3^7 + 3^8 + 2*3^9 + 3^10 + 3^11 + 3^12 + 3^13 + 2*3^14 + 3^15 + 3^16 + 2*3^17 + 2*3^18 + 3^19 + 3^20 + O(3^21))*x + 2 + 2*3^4 + 2*3^6 + 3^8 + 3^9 + 2*3^10 + 2*3^11 + 2*3^12 + 2*3^13 + 2*3^16 + 3^17 + 2*3^18 + 3^19 + O(3^20)
            sage: C = Cluster.from_polynomial(F)
            sage: ascii_art(C)
            '(* * ((* *)_1/4 (* *)_1/4)_1/2)_0'
            sage: ascii_art(Cluster.from_picture(ascii_art(C)))
            '(* * ((* *)_1/4 (* *)_1/4)_1/2)_0'

        Unicode input and output::

            sage: unicode_art(Cluster.from_picture('(● ● ((● ●)_1/4 (● ●)_1/4)_1/2)_0'))
            '(● ● ((● ●)_1/4 (● ●)_1/4)_1/2)_0'


        Negative valuations::

            sage: ascii_art(Cluster.from_picture('(* (* *)_15/2)_-2'))
            '(* (* *)_15/2)_-2'

        Without depths::

            sage: ascii_art(Cluster.from_picture('(* (* *))'))
            '(* (* *))'

        """
        # TODO relax the restriction on depth being digits, but rather anything
        # that can be interpreted as in the input to Cluster()
        S = filter(lambda x: x.isdigit() or x in '()*●/-', S)
        stack = []
        current_depth = ""
        for c in list(S):
            verbose(S)
            if c.isdigit() or c in "/-":
                current_depth += c
                continue
            elif current_depth:  # finalizing a depth
                # update the last child that we just added
                last._depth = QQ(current_depth)
                current_depth = ""

            if c == '(':
                cur = Cluster()
                if stack: # we are not the first cluster
                    cur._parent_cluster = stack[-1]
                    cur._top = stack[-1].top_cluster()
                    stack[-1].children().append(cur)
                stack.append(cur)
            elif c == '*' or c == "●":
                stack[-1].children().append(Cluster([[Infinity]],
                                            top=stack[-1].top_cluster()))
                stack[-1].children()[-1]._parent_cluster = stack[-1]
                for s in stack:
                    s._size += 1
            elif c == ')':
                stack[-1]._children.sort()
                last = stack.pop()
            else:
                raise ValueError("Cluster input malformed")
        if current_depth:
            last._depth = QQ(current_depth)
            for c in last.all_descendants():
                if not c.is_top_cluster():
                    c._depth = c._depth + c.parent_cluster().depth()
        return last

    @classmethod
    def from_BY_tree(cls, T, R):
        r"""
        Construct a Cluster from a (rooted) BY-tree

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import *
            sage: R = Cluster.from_picture("((* *)_4 *)_1")
            sage: T = R.BY_tree()
            sage: Cluster.from_BY_tree(T, R)
            Cluster with 3 roots and 2 children

        """
        Cludict = dict()
        for v in T.depth_first_search(R):
            Cv = Cluster()
            numrs = 0
            numrs = T.weight(v)
            Cludict[v] = Cv
            Cv._size = numrs
            verbose("numrs %s"% numrs)
            verbose(v)
            if v != R:
                verbose(w for w in T.edge_disjoint_paths(v, R)[0][1:] if w in T.blue_vertices())
                # Go up the path towards root till you hit a blue
                parent = next(w for w in T.edge_disjoint_paths(v, R)[0][1:])
                Cv._parent_cluster = Cludict[parent]
                Cv.parent_cluster()._children.append(Cv)
                Cv._depth = Cv.parent_cluster().depth() + T.shortest_path_length(v, parent, weight_function=lambda e: e[2] if T.is_blue(e) else e[2]/2)
                Cv._top = top
                # fix clusters upwards
                w = Cv.parent_cluster()
                while w:
                    w._size += numrs
                    w = w.parent_cluster()
                Cv.parent_cluster()._children.sort()
            else:
                verbose("top")
                top = Cv
                Cv._depth = 0
            for i in range(numrs):
                Cvi = Cluster()
                Cvi._depth = Infinity
                Cvi._size = 1
                Cvi._parent_cluster = Cv
                Cvi._top = top
                Cv._children.append(Cvi)
            Cv._children.sort()
        return top

    @classmethod
    def from_lmfdb_label(cls, S):
        r"""
        Construct a Cluster from an lmfdb label.

        """
        return from_picture(lmfdb_label_to_ascii(S))

    @staticmethod
    def ascii_to_lmfdb_label():
        r"""
        The lmfdb label of the cluster picture, this is defined only for clusters with depths as an alternative representation of the ascii_art.
        
        - c represents an opening bracket
        - ~ is used in place of /
        - _ closes the previous open bracket and the following number (with negatives and possibly /) is the (relative) depth
        - a number in brackets denotes the number of roots there

        """
        s = s.replace(" ", "")
        s = re.sub(r'\*+', lambda M: str(len(M.group(0))), s)
        s = s.replace("(", "c")
        s = s.replace(")", "")
        s = s.replace("/", "~")
        return s

    @staticmethod
    def lmfdb_label_to_ascii(s):
        s = s.replace("c", "(")
        s = s.replace("_", ")_")
        s = s.replace("~", "/")
        s = re.sub(r'\(\d+', lambda M: '(' + int(M.group(0)[1:]) * '*', s)
        s = re.sub(r'\*(?=\*)', '* ', s)
        s = re.sub(r'([\d\*])\(', lambda M: M.group(1) + " (", s)
        return s

    def field_frobenius(self):
        r"""
        Return the frobenius morphism of the base field of ``self``.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: x = polygen(K)
            sage: C = Cluster.from_polynomial((x-1)*(x-6)*(x-26)*(x-126))
            sage: C.field_frobenius()
            Identity endomorphism of 5-adic Field with capped relative precision 150
            sage: C.children()[0].field_frobenius()
            Identity endomorphism of 5-adic Field with capped relative precision 150

        """
        if self.top_cluster()._frobenius_K:
            return self.top_cluster()._frobenius_K
        raise AttributeError("This cluster does not have Frobenius information stored.")

    def parent_cluster(self):
        r"""
        Return the parent cluster of ``self``.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(6), K(26), K(126)])
            sage: C.children()[1].children()[1].children()[1].parent_cluster().parent_cluster()
            Cluster with 3 roots and 2 children

        """
        return self._parent_cluster

    def top_cluster(self):
        r"""
        Return the top cluster for the picture.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(6), K(26), K(126)])
            sage: C.children()[1].children()[1].children()[1].top_cluster().size()
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
            sage: C = Cluster.from_roots([K(1), K(6), K(26), K(126)], leading_coefficient=1)
            sage: C.leading_coefficient()
            1

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
            sage: C.children()[1].children()[1].depth()
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
            sage: C.children()[1].children()[1].relative_depth()
            1


        """
        if self.is_top_cluster():
            return self.depth()
        return self.depth() - self.parent_cluster().depth()

    def size(self):
        r"""
        The size of ``self``, the number of roots contained in the cluster.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.size()
            3
            sage: C = Cluster.from_roots([K(1), K(2), K(5), K(10), K(25)])
            sage: C.size()
            5
            sage: C = Cluster.from_roots([K(1), K(2), K(5), K(10), K(25), K(50)])
            sage: C.size()
            6
            sage: C.children()[2].size()
            4

        """
        return self._size

    def genus(self):
        r"""
        The genus of ``self``, `g` such that number of odd children is
        `2g+1` or `2g+2`.

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
        The genus of the curve on the generic fibre, `g` such that number of roots is `2g+1` or `2g+2`.

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
        Check if ``self`` is even.

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
        Check if ``self`` is odd.

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
        Check if ``self`` is the top cluster for the picture.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.is_top_cluster()
            True
            sage: C.children()[0].is_top_cluster()
            False

        """
        return not self.parent_cluster()

    def is_twin(self):
        r"""
        Check if ``self`` is a twin.

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
        Check if ``self`` is a cotwin.

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

        Returns whether or not ``self`` is proper, i.e. has size at least 2.
        
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

        Returns all children of ``self``.

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

    def all_descendants(self):
        r"""

        Return (an iterator over) all descendent clusters of ``self`` (including ``self``).

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10), K(35), K(135)])
            sage: list(C.all_descendants())
            [Cluster with 5 roots and 2 children,
             Cluster with 1 roots and 0 children,
             Cluster with 4 roots and 2 children,
             Cluster with 1 roots and 0 children,
             Cluster with 3 roots and 2 children,
             Cluster with 1 roots and 0 children,
             Cluster with 2 roots and 2 children,
             Cluster with 1 roots and 0 children,
             Cluster with 1 roots and 0 children]
        """
        yield self
        for C in self.children():
            yield from C.all_descendants()

    def is_ubereven(self):
        r"""
        Check if ``self`` is übereven.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.is_ubereven()
            False
            sage: C.children()[0].is_ubereven()
            False
            sage: C.children()[1].is_ubereven()
            False
            sage: C = Cluster.from_roots([K(1), K(2), K(5), K(10)])
            sage: C.is_ubereven()
            False
            sage: C = Cluster.from_roots([K(1), K(6), K(5), K(10)])
            sage: C.is_ubereven()
            True

        """
        return self.is_even() and all(C.is_even() for C in self.children())

    def _ascii_art_(self):
        r"""
        Return an ascii art representation of ``self``.
        """

        if not self.is_proper():
            return "*"
        return "(" + " ".join(("%s" if c.is_proper() else "%s") % ascii_art(c) for c in self.children()) + ")" + ("_%s" % self.relative_depth() if hasattr(self, "_depth") else "")

    def lmfdb_label(self):
        r"""
        Return the lmfdb label of ``self``.
        """
        return ascii_to_lmfdb_label(_ascii_art_(self))

    def _unicode_art_(self):
        r"""
        Return a unicode art representation of ``self``.
        """

        if not self.is_proper():
            return "●"
        return "(" + " ".join(("%s" if c.is_proper() else "%s") % unicode_art(c) for c in self.children()) + ")" + ("_%s" % self.relative_depth() if hasattr(self, "_depth") else "")

    # TODO simplify by using relative_depth instead of parent_depth
    def latex_internal(self, prefix="m", prev_obj="first"):
        latex_string = ""
        child_cnt = 0
        prevprefix = prev_obj
        if not(self.is_proper()):
            return "\\Root[A] {2} {" + prev_obj + "} {" + prefix + "};\n";
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
        return r"\tikzset{every picture/.append style={scale=1.9}} \def\cdepthscale{0.5}   \clusterpicture" + \
             self.latex_internal() + r"\endclusterpicture"

    def _repr_(self):
        r"""
        Return a string representation of ``self``.

        OUTPUT:

        - a string

        EXAMPLES::

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
        Check if ``self`` is principal, i.e. it is proper, not a twin or a
        cotwin and if `|\mathfrak{s}|=2 g+2` then `\mathfrak{s}` has `\geq 3`
        children.

        EXAMPLES:

        Not-proper::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(3)
            sage: C = Cluster.from_roots([K(1), K(3), K(6)])
            sage: C.children()[0].is_principal()
            False

        Cotwins::

            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10), K(35)])
            sage: C.children()[1].is_principal()
            False
            sage: C = Cluster.from_roots([K(1), K(2), K(10), K(35)])
            sage: C.is_principal()
            False
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.is_principal()
            False

        A twin::

            sage: C.children()[1].is_principal()
            False

        Not enough children::

            sage: C = Cluster.from_roots([K(1), K(6), K(5), K(10)])
            sage: C.is_principal()
            False

        Example 3.6 from the users guide::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(7,150)
            sage: x = polygen(K)
            sage: H = HyperellipticCurve((x^2+7^2)*(x^2-7^(15))*(x-7^6)*(x-7^6-7^9))
            sage: R = Cluster.from_curve(H)
            sage: R.is_principal()
            False
            sage: a = R.children()[2]
            sage: a.is_principal()
            True
        """
        if ((self.is_top_cluster() and self.is_even() and len(self.children()) == 2)
            or any(c.size() == 2*self.top_cluster().curve_genus() for c in self.children())):
            return False
        return self.size() >= 3

    def meet(self, other):
        r"""
        Construct ``self`` `\wedge` ``other``.
        
        EXAMPLES:

        Example 3.6 from the users guide::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(7,150)
            sage: x = polygen(K)
            sage: H = HyperellipticCurve((x^2+7^2)*(x^2-7^(15))*(x-7^6)*(x-7^6-7^9))
            sage: R = Cluster.from_curve(H)
            sage: a = R.children()[2]
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
        Construct ``self*``, if ``self`` is not a cotwin this is the
        smallest cluster containing ``self`` whose parent is not übereven (and
        the top cluster if no such cluster exists). If ``self`` is a cotwin,
        its star is its child of size `2g`.
        
        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(7,150)
            sage: x = polygen(K)
            sage: H = HyperellipticCurve((x^2+7^2)*(x^2-7^(15))*(x-7^6)*(x-7^6-7^9))
            sage: R = Cluster.from_curve(H)
            sage: a = R.children()[2]
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
        `\min_{r\in self}v(z-r) = ` ``self.depth()``

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.is_center(C.center())
            True

            sage: C = Cluster.from_roots([K(1), K(2), K(10), K(35)])
            sage: C.is_center(K(1/5))
            False
            sage: C = Cluster.from_roots([K(1)])
            sage: C.is_center(K(1 + 5))
            False

        TESTS::

            sage: p = 5
            sage: K = Qp(p)
            sage: x = polygen(K)
            sage: C = Cluster.from_polynomial((x-1)*(x-(1+p^2))*(x-(1-p^2))*(x-p)*x*(x-p^3)*(x+p^3))
            sage: for s in C.all_descendants():
            ....:     assert s.is_center(s.center())

        """
        if self.size() == 1:
            return z == self.roots()[0]
        return min((z-r).valuation()/(z-r).parent().absolute_e() for r in self.roots()) == self.depth()

    def center(self):
        r"""
        A choice of center of ``self``, i.e. some `z_{\mathfrak{s}} \in K^{\mathrm{sep}}` with `\min _{r \in \mathfrak{s}} v\left(z_{\mathfrak{s}}-r\right)=d_{\mathfrak{s}}`.

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
            0
            sage: C.is_center(C.center())
            True

            sage: C = Cluster.from_roots([K(1), K(2), K(10), K(35)])
            sage: C.center()
            0
            sage: C.is_center(C.center())
            True

            sage: K = Qp(7,150)
            sage: x = polygen(K)
            sage: H = HyperellipticCurve((x^2+7^2)*(x^2-7^(15))*(x-7^6)*(x-7^6-7^9))
            sage: R = Cluster.from_curve(H)
            sage: a = R.children()[2]
            sage: t1 = a.children()[0]
            sage: t2 = a.children()[1]
            sage: R.is_center(R.center())
            True
            sage: a.is_center(a.center())
            True
            sage: t1.is_center(t1.center())
            True
            sage: t2.is_center(t2.center())
            True

        """
        #S = sum(self.roots())/self.size()
        #if self.is_center(S):
        #    return S
        if self.size() == 1:
            return self._roots[0]

        return teichmuller_trunc(self.roots()[0], self.depth())

    def put_frobenius_action(self, rho):
        rootclusters = [s for s in self.all_descendants() if s.size() == 1]
        for s1 in rootclusters:
            root1 = s1.roots()[0]
            if root1.valuation() >= 0:
                root2 = rho(root1)
            else:
                root2 = rho(root1**(-1))**(-1)
            s2 = [s for s in rootclusters if s.roots()[0] == root2][0]
            while s1:
                s1._frobenius = s2
                s1 = s1.parent_cluster()
                s2 = s2.parent_cluster()
        return None

    def put_inertia_action(self, phi):
        rootclusters = [s for s in self.all_descendants() if s.size() == 1]
        for s1 in rootclusters:
            root1 = s1.roots()[0]
            if root1.valuation() >= 0:
                root2 = phi(root1)
            else:
                root2 = phi(root1**(-1))**(-1)
            s2 = [s for s in rootclusters if s.roots()[0] == root2][0]
            while s1:
                s1._inertia = s2
                s1 = s1.parent_cluster()
                s2 = s2.parent_cluster()
        return None

    # TODO more examples here, and for inertia.
    def frobenius(self):
        r"""
        The action of Frobenius.
        
        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: x = polygen(Qp(7))
            sage: H = HyperellipticCurve((x^2 + 7^2)*(x^2 - 7^15)*(x - 7^6)*(x - 7^6 - 7^9))
            sage: C = Cluster.from_curve(H)
            sage: C.children()[0].frobenius() == C.children()[1]
            True

        """
        if self._frobenius:
            return self._frobenius
        raise AttributeError("This cluster does not have Frobenius information stored.")

    def inertia(self):
        r"""
        The action of a generator of the inertia group.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: x = polygen(Qp(7))
            sage: H = HyperellipticCurve((x^2 + 7^2)*(x^2 - 7^15)*(x - 7^6)*(x - 7^6 - 7^9))
            sage: C = Cluster.from_curve(H)
            sage: C.children()[0].inertia() == C.children()[1]
            False

        """
        if self._inertia:
            return self._inertia
        raise AttributeError("This cluster does not have inertia information stored.")

    # TODO I probably broke this by changing valuations
    def nu(self):
        r"""
        Computes the `\nu` of ``self`` (see section 3)

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: x = polygen(Qp(7))
            sage: H = HyperellipticCurve((x^2 + 7^2)*(x^2 - 7^15)*(x - 7^6)*(x - 7^6 - 7^9))
            sage: C = Cluster.from_curve(H)
            sage: C.children()[2].nu()
            26

        """
        c = self.leading_coefficient()
        F = c.parent()
        p = F(F.prime())
        nu_s = c.valuation() + self.size() * self.depth()
        z = self.center()
        for r in self.top_cluster().roots():
            if r not in self.roots():
                F = r.parent()
                p = F(F.prime())
                nu_s += (r-z).valuation() / p.valuation()
        return nu_s

    def lambda_tilde(self):
        r"""
        Computes the `\tilde\lambda` of ``self`` (see section 3)
        """
        c = self.leading_coefficient()
        F = c.parent()
        p = F(F.prime())
        nu_s = c.valuation() + len(s for s in self.children() if s.is_odd()) * self.depth()
        z = self.center()
        for r in self.top_cluster().roots():
            if not(r in self.roots()):
                F = r.parent()
                p = F(F.prime())
                nu_s += (r-z).valuation() / p.valuation()
        return nu_s/2

    def is_semistable(self, K):
        r"""
        Tests whether the curve associated to ``self`` is semi-stable over `K`.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: x = polygen(Qp(7))
            sage: H = HyperellipticCurve((x^2 + 7^2)*(x^2 - 7^15)*(x - 7^6)*(x - 7^6 - 7^9))
            sage: C = Cluster.from_curve(H)
            sage: C.is_semistable(Qp(7))
            True

        Example 1.4::

            sage: x = polygen(Qp(3))
            sage: H = HyperellipticCurve(x^6 - 27)
            sage: C = Cluster.from_curve(H)
            sage: C.is_semistable(Qp(3))
            False

        """
        F = self.roots()[0].parent()
        eF = F.absolute_e()
        eK = K.absolute_e()
        e = eF / gcd(eF, eK)
        if e > 2:
            return False
        for s in self.all_descendants():
            if s.is_proper() and (s.inertia() != s):
                return False
            if s.is_principal():
                if s.depth() not in ZZ:
                    return False
                if s.nu()/2 not in ZZ:
                    return False
        return True

    def has_good_reduction(self, K):
        r"""
        Tests whether the curve associated to ``self`` has good reduction over `K`.
        
        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(3)
            sage: x = polygen(K)
            sage: H = HyperellipticCurve(x^6 - 27)
            sage: C = Cluster.from_curve(H)
            sage: C.has_good_reduction(K)
            False
            sage: H = HyperellipticCurve(x^3 + 1)
            sage: C = Cluster.from_curve(H)
            sage: C.has_good_reduction(K)
            False
            sage: H = HyperellipticCurve(x^3 + x + 1)
            sage: C = Cluster.from_curve(H)
            sage: C.has_good_reduction(K)
            True
        """
        F = self.roots()[0].parent()
        eF = F.absolute_e()
        eK = K.absolute_e()
        e = eF / gcd(eF, eK)
        if e > 1:
            return False
        g = self.top_cluster().curve_genus()
        for s in self.all_descendants():
            if s.is_proper() and (s.size() < 2*g+1):
                return False
            if s.is_principal():
                if not(s.nu()/2 in ZZ):
                    return False
        return True

    def has_potentially_good_reduction(self):
        r"""
        Tests whether the curve associated to ``self`` has potentially good reduction.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: x = polygen(Qp(3))
            sage: H = HyperellipticCurve(x^6 - 27)
            sage: C = Cluster.from_curve(H)
            sage: C.has_potentially_good_reduction()
            False

            sage: x = polygen(Qp(7))
            sage: H = HyperellipticCurve((x^2 + 7^2)*(x^2 - 7^15)*(x - 7^6)*(x - 7^6 - 7^9))
            sage: C = Cluster.from_curve(H)
            sage: C.has_potentially_good_reduction()
            False

        """
        g = self.top_cluster().curve_genus()
        for s in self.all_descendants():
            if s.is_proper() and (s.size() < 2*g+1):
                return False
        return True

    def jacobian_has_good_reduction(self, K):
        r"""
        Tests whether the curve associated to ``self``'s Jacobian has good reduction over `K`.
        
        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster        
            sage: K = Qp(3)
            sage: x = polygen(K)
            sage: H = HyperellipticCurve(x^6 - 27)
            sage: C = Cluster.from_curve(H)
            sage: C.jacobian_has_good_reduction(K)
            False
            
        """
        F = self.roots()[0].parent()
        eF = F.absolute_e()
        eK = K.absolute_e()
        e = eF / gcd(eF, eK)
        if e > 1:
            return False
        for s in self.all_descendants():
            if not s.is_top_cluster() and s.is_even():
                return False
            if s.is_principal():
                if s.nu()/2 not in ZZ:
                    return False
        return True

    def jacobian_has_potentially_good_reduction(self):
        r"""
        Test whether the curve associated to ``self``'s Jacobian has
        potentially good reduction.
        
        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: x = polygen(Qp(3))
            sage: H = HyperellipticCurve(x^6 - 27)
            sage: C = Cluster.from_curve(H)
            sage: C.jacobian_has_potentially_good_reduction()
            True
            
        """
        for s in self.all_descendants():
            if not s.is_top_cluster() and s.is_even():
                return False
        return True
    
    def potential_toric_rank(self):
        r"""
        Computes the potential toric rank of the Jacobian of the curve.
        
        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: x = polygen(Qp(3))
            sage: H = HyperellipticCurve(x^6 - 27)
            sage: C = Cluster.from_curve(H)
            sage: C.potential_toric_rank()
            0

            sage: C = Cluster.from_picture('(* (* *))')
            sage: C.potential_toric_rank()
            1

            sage: C = Cluster.from_picture('(* * *)')
            sage: C.potential_toric_rank()
            0

        """
        pot_tor_rk = 0
        for s in self.all_descendants():
            if s.is_even() and not s.is_ubereven() and not s.is_top_cluster():
                pot_tor_rk += 1
        if self.top_cluster().is_ubereven():
            pot_tor_rk -= 1
        return pot_tor_rk

    def has_potentially_totally_toric_reduction(self):
        r"""
        Checks whether the curve associated to ``self``'s Jacobian has
        potentially totally toric reduction.
        
        EXAMPLES::
        
            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: x = polygen(Qp(7))
            sage: H = HyperellipticCurve((x^2 + 7^2)*(x^2 - 7^15)*(x - 7^6)*(x - 7^6 - 7^9))
            sage: C = Cluster.from_curve(H)
            sage: C.has_potentially_totally_toric_reduction()
            True
            
        """
        return self.potential_toric_rank() == self.top_cluster().curve_genus()

    def minimal_discriminant(self):
        r"""
        Computes the valuation of the minimal discriminant of the curve.
        This is only implemented for semi-stable curves.
        
        EXAMPLES::
        
            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: x = polygen(Qp(7))
            sage: f = (x^3 - 7^15)*(x^2-7^6)*(x^3-7^3)
            sage: Cluster.from_polynomial(f).minimal_discriminant()
            24
            sage: f = 7*(x^2+1)*(x^2+36)*(x^2+64)
            sage: Cluster.from_polynomial(f).minimal_discriminant()
            22

        """
        c = self.leading_coefficient()
        assert(self.is_semistable(c.parent()))
        g = self.curve_genus()
        discC = c.valuation() * (4*g + 2) + self.depth()*self.size()*(self.size()-1)
        for s in self.all_descendants():
            if s.is_proper():
                discC += s.relative_depth()*s.size()*(s.size()-1)

        E = 0
        if ( (c.valuation() % 2) == 1) and len(self.children()) == 2:
            if self.children()[0].frobenius() == self.children()[1]:
                E = 1
        error_term = c.valuation() - E + self.depth()*(self.size()-g-1)
        for s in self.all_descendants():
            if g+1 < s.size():
                error_term += s.relative_depth()*(s.size() - g - 1)

        return discC - (4*g+2)*error_term

    def homology_of_special_fibre(self):
        r"""
        Computes H1 together with a Frobenius action if possible

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: p = 23
            sage: x = polygen(Qp(p))
            sage: H = HyperellipticCurve(((x^2+1)^2 - 2*x^2*p^4 + 2*p^4 + p^8)*(x-2)*(x-3))
            sage: C = Cluster.from_curve(H)
            sage: H1, frob = C.homology_of_special_fibre()
            sage: L = [b for b in H1.basis()]
            sage: frob(L[0]) == L[1]
            True

        """
        A = [s for s in self.all_descendants() if s.is_even() and not s.is_ubereven()  and s != s.top_cluster()]
        ZA = CombinatorialFreeModule(ZZ, A)
        frob_clusters = lambda s : s.frobenius()

        if self.is_ubereven():
            B = [s for s in A if s.star() == s.top_cluster()]
            basis1 = [ZA(s) for s in A if s not in B]
            basis2 = [ZA(s) - ZA(B[0]) for s in B if s != B[0]]
            basis = basis1 + basis2
            H1 = ZA.submodule(basis)
            if self._roots:
                frob_on_basis = lambda s : self.epsilon(frob_clusters, self.field_frobenius())*ZA(s.frobenius())
                frobZA = ZA.module_morphism(on_basis=frob_on_basis, codomain=ZA)

                #frob_on_basis1 = [ZA(s.frobenius()) for s in A if not(s in B)]
                #frob_on_basis2 = [ZA(s.frobenius()) - ZA(B[0].frobenius()) for s in B if s != B[0]]
                #frob_on_basis3 = frob_on_basis1 + frob_on_basis2
                frob_on_basis = lambda s : frobZA(basis[s])
                frob = H1.module_morphism(on_basis=frob_on_basis, codomain=H1)
                return H1, frob
            else:
                return H1
        else:
            H1 = ZA
            if self._roots:
                frob_on_basis = lambda s : self.epsilon(frob_clusters, self.field_frobenius())*ZA(s.frobenius())
                frob = H1.module_morphism(on_basis=frob_on_basis, codomain=H1)
                return H1, frob
            else:
                return H1

    def root_number(self):
        r"""
        Computes the root number of ``self``.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: p = 23
            sage: x = polygen(Qp(p))
            sage: H = HyperellipticCurve(((x^2+1)^2 - 2*x^2*p^4 + 2*p^4 + p^8)*(x-2)*(x-3))
            sage: C = Cluster.from_curve(H)
            sage: C.root_number()
            -1

        """
        if not self.is_semistable(self.leading_coefficient().parent()):
            raise TypeError("Cluster is not semi-stable")
        H1, frob = self.homology_of_special_fibre()
        frob_minus_identity = H1.module_morphism(lambda i : frob(H1.monomial(i)) - H1.monomial(i), codomain=H1)
        K = frob_minus_identity.kernel()
        return (-1)**K.rank()

    def theta_squared(self):
        r"""
        `c \prod_{r \notin \mathfrak{s}}\left(z_{\mathfrak{s}}-r\right)`.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: p = 5
            sage: K = Qp(p)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)])
            sage: C.theta_squared()
            Traceback (most recent call last):
            ...
            AttributeError: This cluster does not have a leading coefficient stored.
            sage: x = polygen(K)
            sage: C = Cluster.from_polynomial((x-1)*(x-(1+p^2))*(x-(1-p^2))*(x-p)*x*(x-p^3)*(x+p^3))
            sage: C.theta_squared()
            1 + O(5^20)
            sage: D = C.children()[1]
            sage: D.theta_squared() == 624
            True
            sage: K = Qp(7,150)
            sage: x = polygen(K)
            sage: H = HyperellipticCurve((x^2+7^2)*(x^2-7^(15))*(x-7^6)*(x-7^6-7^9))
            sage: R = Cluster.from_curve(H)
            sage: a = R.children()[0]
            sage: #a.theta() TODO renable

        """
        return self.leading_coefficient()*prod(self.center() - r for r in self.top_cluster().roots() if r not in self.roots())

    def theta(self):
        r"""
        A choice of `\sqrt{c \prod_{r \notin \mathfrak{s}}\left(z_{\mathfrak{s}}-r\right)}`.

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
            sage: D = C.children()[1]
            sage: D.theta()
            2 + 5 + 2*5^2 + 5^3 + 2*5^4 + 5^5 + 4*5^6 + 2*5^7 + 2*5^8 + 2*5^9 + 5^10 + 4*5^11 + 2*5^13 + 3*5^14 + 4*5^15 + O(5^16)
            sage: K = Qp(7,150)
            sage: x = polygen(K)
            sage: H = HyperellipticCurve((x^2+7^2)*(x^2-7^(15))*(x-7^6)*(x-7^6-7^9))
            sage: R = Cluster.from_curve(H)
            sage: a = R.children()[0]
            sage: #a.theta() TODO renable

        """
        return self.theta_squared().sqrt()

    # TODO
    def epsilon(self, sigma, sigmaK):
        r"""
        .. MATH::

            \frac{\sigma\left(\theta_{s^{*}}\right)}{\theta_{\left(\sigma_{\mathfrak{s}}\right)^{*}}} \bmod \mathfrak{m} \in\{\pm 1\} \text { if } \mathfrak{s} \text { even or cotwin, } \epsilon_{\mathfrak{s}}(\sigma)=0 \text { otherwise }

        INPUT:

        - ``sigma`` an element of Galois acting on clusters
        - ``sigmaK`` an element of Galois as a map `K \to K`

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: C = Cluster.from_roots([K(1), K(5), K(10)], leading_coefficient=1)
            sage: C.epsilon(lambda x: x, lambda x: x)
            1
            sage: C = Cluster.from_roots([K(1), K(2), K(10), K(35)], leading_coefficient=1)
            sage: C.children()[0].epsilon(lambda x: x, lambda x: x)
            0

        """
        if self.is_even() or self.is_cotwin():
            if sigma(self) == self:
                P = self.star().theta_squared()
                assert sigmaK(P) == P
                assert P.valuation() % 2 == 0
                #return sigma(P.sqrt()) / P.sqrt()
                # we know that sigma(P.sqrt()) = +-P.sqrt()
                # so it suffices
                if P.unit_part().residue().is_square():
                    sqrtP = P.parent( P.unit_part().residue().square_root() )
                    if sigmaK(sqrtP).residue() == sqrtP.residue():
                        return 1
                    else:
                        return -1
                else:
                    return -1

            # TODO this codepath is kinda busted, i think we want the residue of this
            return sigma(self.star().theta())\
                 / sigma(self).star().theta()
        return 0

    def BY_tree(self, with_frob=False, check=True):
        r"""

        Constructs the BY-tree associated to the cluster picture, and optionally
        the associated :class:`BYTreeIsomorphism` to Frobenius acting on the cluster.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster, BYTree
            sage: K = Qp(7,150)
            sage: x = polygen(K)
            sage: H = HyperellipticCurve((x^2+7^2)*(x^2-7^(15))*(x-7^6)*(x-7^6-7^9))
            sage: R = Cluster.from_curve(H)
            sage: R.BY_tree()
            BY-tree with 1 yellow vertices, 3 blue vertices, 3 yellow edges, 0 blue edges
            sage: K = Qp(5)
            sage: R = Cluster.from_roots([K(1), K(6), K(2), K(7)])
            sage: R.BY_tree()
            BY-tree with 0 yellow vertices, 2 blue vertices, 1 yellow edges, 0 blue edges

        """
        assert self.is_top_cluster()
        T = BYTree(name="BY-tree of %s" % self)
        for s in self.all_descendants():
            verbose(s)
            if s.is_proper():
                if s.is_ubereven():
                    T.add_yellow_vertex(s)
                else:
                    T.add_blue_vertex(s, s.genus())
                if s.parent_cluster():
                    if s.is_even():
                        T.add_yellow_edge((s, s.parent_cluster(), 2*s.relative_depth()))
                    else:
                        T.add_blue_edge((s, s.parent_cluster(), s.relative_depth()))

        if (self.is_even() and len(self.children()) == 2):
            T.delete_vertex(self)
            if self.children()[0].is_proper() and self.children()[1].is_proper():
                if self.children()[0].is_even():
                    T.add_yellow_edge((self.children()[0],
                                       self.children()[1],
                                       2*self.children()[0].relative_depth() +
                                       2*self.children()[1].relative_depth()))
                else:
                    T.add_blue_edge((self.children()[0],
                                     self.children()[1],
                                     self.children()[0].relative_depth() +
                                     self.children()[1].relative_depth()))


        verbose(T)
        assert T.validate()

        if with_frob:
            F = BYTreeIsomorphism(T, T, lambda x: x.frobenius(),
                    lambda Y: T.sign_vertex(Y).star().epsilon(lambda x:
                                x.frobenius(), self.field_frobenius()))

            return (T, F)

        return T

    def tamagawa_number(self):
        r"""
        Compute the Tamagawa number of ``self``.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster
            sage: K = Qp(5)
            sage: x = polygen(K)
            sage: R = Cluster.from_polynomial((x^4-5^4)*(x+1)*(x+2))
            sage: R.tamagawa_number()
            2

        Elliptic curve 15.a1::

            sage: E = EllipticCurve("15.a1")
            sage: E.tamagawa_number(3)
            2
            sage: E = E.short_weierstrass_model(complete_cube=False).change_ring(Qp(3))
            sage: R = Cluster.from_curve(E)
            sage: R.tamagawa_number()
            2

        Elliptic curve 576.c4::

            sage: E = EllipticCurve([9, 0])
            sage: E.tamagawa_number(3)
            2
            sage: E = E.short_weierstrass_model(complete_cube=False).change_ring(Qp(3))
            sage: R = Cluster.from_curve(E)
            sage: R.is_semistable(Qp(3))
            False
            sage: R.tamagawa_number()
            Traceback (most recent call last):
            ...
            AssertionError

        """
        assert self.is_semistable(self.leading_coefficient().parent())
        T, F = self.BY_tree(with_frob=True)
        return T.tamagawa_number(F)

    def __hash__(self):
        return hash(id(self))

    def __eq__(self, other):
        return self is other

    def __ne__(self, other):
        return self is not other

    def __lt__(self, other):
        if self.size() != other.size():
            return self.size() < other.size()
        if self.size() > 1:
            if self.depth() != other.depth():
                return self.depth() < other.depth()
        if self.children() != other.children():
            return self.children() < other.children()
        return id(self) < id(other)


# TODO probably remove this pointless wrapper
def orbit_decomposition(F, S, cond=None):
    r"""
    Decompose a list ``S`` into orbits under the function ``F``, returning only
    those satisfying ``cond``.

    EXAMPLES::

        sage: from sage_cluster_pictures.cluster_pictures import orbit_decomposition
        sage: orbit_decomposition(lambda x: x + 1, list(Integers(15)))
        [[14, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
        sage: orbit_decomposition(lambda x: x + 1, list(Integers(15)), cond = lambda x: len(x) < 1)
        []
    """
    D = FiniteDynamicalSystem(S, F)
    orbits = D.cycles()
    if cond:
        return [mo for mo in orbits if cond(mo)]
    return orbits


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
            BY-tree with 0 yellow vertices, 0 blue vertices, 0 yellow edges, 0 blue edges

        TESTS::

            sage: #C = BYTree()
            sage: #TestSuite(C).run()
        """
        kwargs['weighted'] = True
        kwargs['sparse'] = True
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
            BY-tree with 0 yellow vertices, 1 blue vertices, 0 yellow edges, 0 blue edges
            sage: T.add_blue_vertex('v2', 1)
            sage: T
            BY-tree with 0 yellow vertices, 2 blue vertices, 0 yellow edges, 0 blue edges
            sage: T.add_blue_vertex('v3')
            sage: T.genus('v3')
            0

        """
        self.add_vertex(label)
        self._genera[label] = genus
        self._blue_vertices.append(label)

    def add_blue_vertices(self, labels, genera=None):
        r"""
        Adds a sequence of blue vertices given by ``labels`` to ``self``, optionally with genera.

        INPUT:

        - ``labels`` - an iterable containing valid inputs for :meth:``add_blue_vertex``.
        - ``genera`` (optional) - an iterable containing the same number of inputs as ``labels``, specifying a genus for each vertex.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertices(['b1', 'b2', 'b3', 'b4', 'b5', 'b6', 'b7'])
            sage: T.add_yellow_vertex('Y')
            sage: T.add_blue_edges([('b1', 'Y', 2), ('b2', 'Y', 2), ('b5', 'Y', 1), ('b6', 'Y', 4), ('b3', 'b4', 1), ('b7', 'b4', 1)])
            sage: T
            BY-tree with 1 yellow vertices, 7 blue vertices, 0 yellow edges, 6 blue edges
            sage: T.add_blue_vertices(['b8', 'b9'], [1, 2])
            sage: T
            BY-tree with 1 yellow vertices, 9 blue vertices, 0 yellow edges, 6 blue edges

        """
        if genera:
            for l, g in zip(labels, genera):
                self.add_blue_vertex(l, g)
        else:
            for l in labels:
                self.add_blue_vertex(l)

    def add_yellow_vertex(self, label):
        r"""

        Adds a yellow vertex to the BY-tree.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_yellow_vertex('v1')
            sage: T
            BY-tree with 1 yellow vertices, 0 blue vertices, 0 yellow edges, 0 blue edges
            sage: T.add_yellow_vertex('v2')
            sage: T
            BY-tree with 2 yellow vertices, 0 blue vertices, 0 yellow edges, 0 blue edges

        """
        self.add_vertex(label)
        self._genera[label] = 0
        self._yellow_vertices.append(label)

    def add_yellow_vertices(self, labels):
        r"""
        Adds a sequence of yellow vertices given by ``labels`` to ``self``.

        INPUT:

        - ``labels`` - an iterable containing valid inputs for :meth:``add_yellow_vertex``.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_yellow_vertices(['b1', 'b2', 'b3', 'b4', 'b5', 'b6', 'b7'])
            sage: T.add_yellow_vertex('Y')
            sage: T
            BY-tree with 8 yellow vertices, 0 blue vertices, 0 yellow edges, 0 blue edges

        """
        for l in labels:
            self.add_yellow_vertex(l)

    def delete_vertex(self, label):
        r"""

        Deletes a vertex and all incident edges from the BY-tree.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_yellow_vertex('v1')
            sage: T.add_yellow_vertex('v2')
            sage: T.add_blue_edge(('v1','v2',2))
            sage: T.delete_vertex('v1')
            sage: T
            BY-tree with 1 yellow vertices, 0 blue vertices, 0 yellow edges, 0 blue edges
            sage: T = BYTree()
            sage: T.add_yellow_vertex('v1')
            sage: T.add_yellow_vertex('v2')
            sage: T.add_blue_edge(('v2','v1',2))
            sage: T.delete_vertex('v1')
            sage: T
            BY-tree with 1 yellow vertices, 0 blue vertices, 0 yellow edges, 0 blue edges
            sage: T = BYTree()
            sage: T.add_yellow_vertex('v1')
            sage: T.add_yellow_vertex('v2')
            sage: T.add_yellow_edge(('v1','v2',2))
            sage: T.delete_vertex('v1')
            sage: T
            BY-tree with 1 yellow vertices, 0 blue vertices, 0 yellow edges, 0 blue edges
            sage: T = BYTree()
            sage: T.add_yellow_vertex('v1')
            sage: T.add_yellow_vertex('v2')
            sage: T.add_yellow_edge(('v2','v1',2))
            sage: T.delete_vertex('v1')
            sage: T
            BY-tree with 1 yellow vertices, 0 blue vertices, 0 yellow edges, 0 blue edges

        """
        super().delete_vertex(label)
        self._prune_colour_lists()

    def weight(self, v):
        r"""
        Returns the weight of a vertex of ``self``, defined by `w: V\left(self\right) \rightarrow \mathbb{Z}`

        .. MATH::
            w(v)=\left\{\begin{array}{ll}2 g(v)+2-\text { #blue edges at } v & \text { if } v \text { is blue, } \\ 0 & \text { if } v \text { is yellow }\end{array}\right.

        """
        if v in self.blue_vertices():
            return 2*self.genus(v) + 2 - sum(1 for b in self.edges_incident(v) if self.is_blue(b))
        return 0 # yellow

    def blue_vertices(self):
        r"""

        Returns the list of blue vertices of ``self``.

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

        Returns the list of yellow vertices of ``self``.

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

        - ``a`` - triple of vertices and a weight.


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
            BY-tree with 2 yellow vertices, 2 blue vertices, 2 yellow edges, 1 blue edges
        """


        self.add_edge(a)
        e = next(ee for ee in self.edges_incident(a[0])
                 if ee[0] == a[1] or ee[1] == a[1])
        verbose(e)
        self._blue_edges.append(e)

    def add_blue_edges(self, B):
        r"""
        Adds a sequence of blue edges ``B`` to ``self``.

        INPUT:

        - ``B`` - an iterable containing valid inputs for :meth:``add_blue_edge``.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertices(['b1', 'b2', 'b3', 'b4', 'b5', 'b6', 'b7'])
            sage: T.add_yellow_vertex('Y')
            sage: T.add_blue_edges([('b1', 'Y', 2), ('b2', 'Y', 2), ('b5', 'Y', 1), ('b6', 'Y', 4), ('b3', 'b4', 1), ('b7', 'b4', 1)])
            sage: T
            BY-tree with 1 yellow vertices, 7 blue vertices, 0 yellow edges, 6 blue edges

        """
        for b in B:
            self.add_blue_edge(b)

    def add_yellow_edges(self, Y):
        r"""
        Adds a sequence of yellow edges ``Y`` to ``self``.

        INPUT:

        - ``Y`` - an iterable containing valid inputs for :meth:``add_yellow_edge``.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree(name="Stick person")
            sage: T.add_blue_vertices(['b1', 'b2', 'b3', 'b4', 'b5', 'b6', 'b7'])
            sage: T.add_yellow_vertex('Y')
            sage: T.add_yellow_edges([('b1', 'Y', 2), ('b2', 'Y', 2), ('b5', 'Y', 1), ('b6', 'Y', 4), ('b3', 'b4', 1), ('b7', 'b4', 1)])
            sage: T.add_blue_edge(('b6', 'b4', 1))
            sage: T
            BY-tree with 1 yellow vertices, 7 blue vertices, 6 yellow edges, 1 blue edges

        """
        for y in Y:
            self.add_yellow_edge(y)

    def add_yellow_edge(self, a):
        r"""

        Adds a yellow edge to the BY-tree.

        INPUT:

        - ``a`` - triple of vertices and a weight.

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
            BY-tree with 2 yellow vertices, 2 blue vertices, 2 yellow edges, 1 blue edges

        """
        self.add_edge(a)
        e = next(ee for ee in self.edges_incident(a[0]) if ee[0] == a[1] or ee[1] == a[1])
        verbose(e)
        self._yellow_edges.append(e)

    def blue_edges(self):
        r"""

        Returns the list of yellow vertices of ``self``.

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

        Returns the list of yellow edges of ``self``.

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

    def is_blue(self, e):
        r"""

        Check if an edge `e` of ``self`` is blue.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 2)
            sage: T.add_blue_vertex('v3', 2)
            sage: T.add_yellow_edge(('v2', 'v1', 1))
            sage: T.is_blue(T.edges()[0])
            False
            sage: T.add_blue_edge(('v3', 'v1', 1))
            sage: T.is_blue(T.edges_incident('v3')[0])
            True

        """
        verbose(e, level=2)
        return e in self._blue_edges or (e[1], e[0], e[2]) in self._blue_edges

    def is_yellow(self, e):
        r"""

        Check if an edge `e` of ``self`` is yellow.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 2)
            sage: T.add_blue_vertex('v3', 2)
            sage: T.add_yellow_edge(('v2', 'v1', 1))
            sage: T.is_yellow(T.edges()[0])
            True
            sage: T.add_blue_edge(('v3', 'v1', 1))
            sage: T.is_yellow(T.edges_incident('v3')[0])
            False

        """
        verbose(e, level=2)
        return e in self._yellow_edges or (e[1], e[0], e[2]) in self._yellow_edges

    def _repr_(self):
        r"""

        Returns a string representation of ``self``.

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
            BY-tree with 2 yellow vertices, 2 blue vertices, 2 yellow edges, 1 blue edges

        """
        return "BY-tree with %s yellow vertices, %s blue vertices, %s yellow edges, %s blue edges" % (len(self.yellow_vertices()), len(self.blue_vertices()), len(self.yellow_edges()), len(self.blue_edges()))

    def validate(self):
        r"""

        Checks if ``self`` is a valid BY-tree, i.e. it is a tree, all vertices / edges are coloured blue or yellow, all edges have a positive weight, all vertices have nonnegative genus, and:
        (1) yellow vertices have genus 0, degree `\ge 3`, and only yellow edges;
        (2) blue vertices of genus 0 have at least one yellow edge;
        (3) at every vertex, `2g(v) + 2 \ge \#` blue edges at `v`.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree, Cluster
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
            sage: p = 3
            sage: K = Qp(p)
            sage: C = Cluster.from_roots([K(1), K(p), K(2*p), K(2*p + p^2), K(2*p + 2*p^2), K(2*p + 2*p^2+p^3)])
            sage: C.BY_tree().validate()
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
        if not all(all(self.is_yellow(e) for e in self.edges_incident(y))
                   for y in self.yellow_vertices()):
            verbose("yellow vertex with non-yellow edge")
            return False

        if not all(any(self.is_yellow(e)
                       for e in self.edges_incident(v))
                   for v in self.blue_vertices() if self.genus(v) == 0):
            verbose("blue genus zero vertex without yellow edge")
            return False
        if not all(2*self.genus(v) + 2 >=
                   len([e for e in self.edges_incident(v)
                       if self.is_blue(e)])
                   for v in self.vertices()):
            verbose("2g+2 less than number of blue edges leaving a vertex")
            return False

        return True

    # TODO doc this based on super
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
        verbose(options, level=2)
        return super().graphplot(**options)

    def subgraph(self, *args, **options):
        G = super().subgraph(*args, **options)
        G._yellow_vertices = [v for v in G.vertices() if v in self.yellow_vertices()]
        G._blue_vertices = [v for v in G.vertices() if v in self.blue_vertices()]
        G._yellow_edges = [e for e in G.edges() if self.is_yellow(e)]
        G._blue_edges = [e for e in G.edges() if self.is_blue(e)]
        verbose(self._genera)
        G._genera = {b: self.genus(b) for b in G.blue_vertices()}
        return G

    def blue_subgraph(self):
        r"""
        Return the blue subgraph  of ``self``, i.e. the subgraph consisting of
        blue edges and vertices. Note that by assumption no blue edge is
        incident to a yellow vertex.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 0)
            sage: T.add_yellow_edge(('v1', 'v2', 2))
            sage: T.blue_subgraph()
            BY-tree with 0 yellow vertices, 2 blue vertices, 0 yellow edges, 0 blue edges

        """
        B = self.subgraph(vertices=self.blue_vertices(),
                          edges=self.blue_edges())
        B._blue_edges = self.blue_edges()
        B._blue_vertices = self.blue_vertices()
        return B

    def yellow_components(self):
        r"""
        Return the set of yellow components of ``self``, i.e. the connected
        components of ``self`` `\smallsetminus` ``self.blue_subgraph()``,
        as a list of yellow edges in the component.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 0)
            sage: T.add_yellow_edge(('v1', 'v2', 2))
            sage: T.yellow_components()
            [[('v1', 'v2', 2)]]

        """
        components = []
        for y in self.yellow_edges():
            for C in components:
                if y[0] in self.yellow_vertices() and\
                   any(y[0] == v1 or y[0] == v2 for v1, v2, _ in C):
                    C.append(y)
                    break
                if y[1] in self.yellow_vertices() and\
                   any(y[1] == v1 or y[1] == v2 for v1, v2, _ in C):
                    C.append(y)
                    break
            else:
                components.append([y])
        return components

    def sign_vertex(self, component):
        r"""
        Return the vertex of ``self`` used to compute the sign of the yellow
        component ``component`` in an automorphism.
        This is any vertex in the closure of ``component``, which is either
        yellow or not the parent of a cluster `\mathfrak t` with
        `v_{\mathfrak t}` also in this closure.

        NOTE:

        This depends on parent child relationships of vertices, so does not
        work for arbitrary BY-trees, only those coming from clusters.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster, BYTree
            sage: x = polygen(Qp(7))
            sage: H = HyperellipticCurve((x^2 + 7^2)*(x^2 - 7^15)*(x - 7^6)*(x - 7^6 - 7^9))
            sage: R = Cluster.from_curve(H)
            sage: T = R.BY_tree()
            sage: T.sign_vertex([T.yellow_edges()[0]])
            Cluster with 4 roots and 2 children

        """
        # Find connected components of self - B, we do this by starting at
        # all yellow edges and connecting to others when they share a yellow
        # vertex only
        verts_in_component = sum([[Y[0], Y[1]] for Y in component], [])
        for s in verts_in_component:
            if s in self.yellow_vertices():
                verbose("found yellow vertex")
                return s
            if all(t not in verts_in_component for t in s.children()):
                verbose("found vertex with no children in component")
                return s

    def degree_ge_three_vertices(self):
        r"""
        Return all degree `\ge 3` vertices of ``self``.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster, BYTree
            sage: x = polygen(Qp(7))
            sage: H = HyperellipticCurve((x^2 + 7^2)*(x^2 - 7^15)*(x - 7^6)*(x - 7^6 - 7^9))
            sage: T = Cluster.from_curve(H).BY_tree()
            sage: T.degree_ge_three_vertices()
            [Cluster with 4 roots and 2 children]
            sage: K = Qp(5)
            sage: x = polygen(K)
            sage: R = Cluster.from_polynomial((x^4-5^4)*(x+1)*(x+2))
            sage: T = R.BY_tree()
            sage: T.degree_ge_three_vertices()
            []
            sage: T = BYTree()
            sage: T.add_blue_vertex(1)
            sage: T.add_blue_vertex(2)
            sage: T.add_blue_vertex(3)
            sage: T.add_blue_vertex(4)
            sage: T.add_yellow_vertex(5)
            sage: T.add_yellow_edge((1, 5, 1))
            sage: T.add_yellow_edge((2, 5, 1))
            sage: T.add_yellow_edge((3, 5, 1))
            sage: T.add_yellow_edge((4, 5, 1))
            sage: T.degree_ge_three_vertices()
            [5]

        """
        return [v for v in self.vertices() if self.degree(v) >= 3]

    def quotient(self, F):
        r"""
        Quotient ``self`` by the automorphism ``F``.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import Cluster, BYTree
            sage: K.<a> = Qq(11^3,20)
            sage: z = K.teichmuller(4*a^2 + 3)
            sage: x = polygen(K)
            sage: f = x*(x-1)*(x-2)*(x-z+11)*(x-z-11)*(x-z^2+11)*(x-z^2-11)*(x-z^4+11)*(x-z^4-11)
            sage: x = polygen(Qp(11))
            sage: f = sage_eval(str(f), locals={'x':x})
            sage: R = Cluster.from_polynomial(f)
            sage: T, F = R.BY_tree(with_frob=True)
            sage: T.quotient(F)
            BY-tree with 0 yellow vertices, 2 blue vertices, 1 yellow edges, 0 blue edges
            sage: x = polygen(Qp(7))
            sage: H = HyperellipticCurve((x^2 + 7^2)*(x^2 - 7^15)*(x - 7^6)*(x - 7^6 - 7^9))
            sage: R = Cluster.from_curve(H)
            sage: T, F = R.BY_tree(with_frob=True)
            sage: T.quotient(F)
            BY-tree with 1 yellow vertices, 3 blue vertices, 3 yellow edges, 0 blue edges

        """
        T = BYTree(name="Quotient tree of %s by %s" % (self, F))
        orbs = orbit_decomposition(F, self.vertices())
        verbose(orbs)
        for o in orbs:
            # all the vertices in the orbit are blue?
            if o[0] in self.blue_vertices():
                T.add_blue_vertex(tuple(o))
            else:
                T.add_yellow_vertex(tuple(o))
        for o1, o2 in Combinations(orbs, 2):
            last = None
            q = 0
            for e in self.edges():
                if ((e[0] in o1 and e[1] in o2)
                 or (e[1] in o1 and e[0] in o2)):
                    last = e
                    q += 1
            if last:
                if self.is_yellow(last):
                    T.add_yellow_edge((tuple(o1), tuple(o2), last[2]/q))
                else:
                    T.add_blue_edge((tuple(o1), tuple(o2), last[2]/q))

        return T

    def multiway_cuts(self, vertices):
        r"""
        Return all unordered `n`-tuples of edges of ``self`` such that their
        removal disconnects the `n + 1` ``vertices`` provided.

        TODO:

        This doesn't really need a BY-tree

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree
            sage: G = BYTree()
            sage: G.add_yellow_vertex(1)
            sage: G.add_yellow_vertex(2)
            sage: G.add_yellow_edge((1,2,1))
            sage: list(G.multiway_cuts([1,2]))
            [[(1, 2, 1)]]
            sage: G.add_yellow_vertex(3)
            sage: G.add_yellow_edge((2,3,1))
            sage: list(G.multiway_cuts([1,2,3]))
            [[(1, 2, 1), (2, 3, 1)]]
            sage: list(G.multiway_cuts([1,3]))
            [[(1, 2, 1)], [(2, 3, 1)]]
            sage: G.add_yellow_edge((1,3,1))
            sage: list(G.multiway_cuts([1,3]))
            []
            sage: list(G.multiway_cuts([1,2,3]))
            []
            sage: list(G.multiway_cuts([1,2,3]))
            []
            sage: G.add_yellow_vertex(4)
            sage: G.add_yellow_edge((2,4,1))
            sage: list(G.multiway_cuts([1,2,3]))
            []
            sage: list(G.multiway_cuts([1,2,4]))
            []

        """
        for es in Combinations(self.edges(), len(vertices) - 1):
            D = copy(self)
            D.delete_edges(es)
            if len(set(tuple(D.connected_component_containing_vertex(v)) for v in vertices)) == len(vertices):
                yield es

    def _prune_colour_lists(self):
        self._blue_vertices = [v for v in self._blue_vertices if v in self.vertices()]
        self._yellow_vertices = [v for v in self._yellow_vertices if v in self.vertices()]
        self._blue_edges = [e for e in self._blue_edges if e in self.edges()]
        self._yellow_edges = [e for e in self._yellow_edges if e in self.edges()]
        self._genera = {k: self._genera[k] for k in self._genera if k in self.vertices()}

    def contract_odd_order_subtree(self, F):
        r"""
        Returns a BY-tree obtained from ``self`` by contracting the subtree on
        which ``F`` acts with odd order into a blue vertex, along with the
        induced :class:`BYTreeIsomorphism` of ``F`` on the new tree.
        Note that this mutates the original graph.
        """
        odd_vertices = sum(orbit_decomposition(F, self.vertices(),
                           cond=lambda x: len(x) % 2 == 1), [])
        self._blue_vertices = [v for v in self.vertices()
                               if v in self._blue_vertices or odd_vertices]
        self._yellow_vertices = [v for v in self._yellow_vertices
                                 if v in self.vertices()
                                 and v not in odd_vertices]
        verbose(odd_vertices)
        edges = [e for e in self.edges()
                 if e[0] in odd_vertices and e[1] in odd_vertices]
        verbose(edges)
        self.contract_edges(edges)
        verbose(self.vertices())

        self._prune_colour_lists()

        newF = BYTreeIsomorphism(self, self,
                                 lambda x: x if x in vertices else F(x),
                                 lambda Y: F.epsilon(Y))

        return self, F

    def tamagawa_number(self, F):
        r"""
        Compute the Tamagawa number of ``self`` with respect to the
        automorphism ``F``.

        INPUT:

        - ``F`` - A :class:`BYTreeIsomorphism` from ``self`` to ``self``.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree, Cluster
            sage: K = Qp(5)
            sage: x  = polygen(K)
            sage: R = Cluster.from_polynomial((x^4-5^4)*(x+1)*(x+2))
            sage: T, F = R.BY_tree(with_frob=True)
            sage: T.tamagawa_number(F)
            2

        """
        # TODO examples
        B = self.blue_subgraph()
        verbose(len(B.vertices()))
        verbose(len(B.edges()))
        components = self.yellow_components()
        verbose(components)

        # Decompose the components found into orbits under frobenius
        # TODO this doesn't work yet, it is combinatorially annoying
        def in_comp(e, D): # check if an edge lies in a component
            for y in D:
                if ((y[0] == e[0] and y[1] == e[1])
                 or (y[1] == e[0] and y[0] == e[1])):
                    return True
            return False

        orbits = []
        for C in components:
            verbose(orbits)
            verbose(C)
            Fe = (F(C[0][0]), F(C[0][1]), C[0][2])
            verbose(Fe)
            for i in range(len(orbits)):
                verbose(i)
                O = orbits[i]
                verbose(O)
                if in_comp(Fe, O[0]):
                    verbose("Fe matches O start")
                    orbits[i] = [C] + O
                    for i2 in range(len(orbits)):
                        O2 = orbits[i2]
                        Fe = (F(O2[-1][0][0]), F(O2[-1][0][1]), O2[-1][0][2])
                        if in_comp(Fe, C):
                            verbose("Fe matches O2 end")
                            if i != i2:
                                orbits[i] = orbits[i] + O2
                                orbits[i2] = []
                            break
                    break
                verbose("didn't  match")
            else:
                verbose("else") # TODO is this case needed?
                for i in range(len(orbits)):
                    verbose(i)
                    O = orbits[i]
                    Fe = (F(O[-1][0][0]), F(O[-1][0][1]), O[-1][0][2])
                    if in_comp(Fe, C):
                        orbits[i] = O + [C]
                        break
                else:
                    verbose("adding new orbit")
                    orbits += [[C]]
        orbits = [o for o in orbits if o]
        verbose(orbits)

        ans = 1
        verbose("Step %s" % 1)
        for orb in orbits:
            verbose(orb)
            C = orb[0]  # choice of a component in the orbit
            verbose(C)

            verbose("Step %s" % 2)
            # T_i the induced subgraph by the yellow component
            Torb = self.subgraph(vertices=sum(([y[0],y[1]] for y in C), []),
                                 edges=C)
            verbose(Torb)

            verbose("Step %s" % 3)
            Borb = Torb.blue_vertices() # B_i
            assert len(Borb) > 0
            verbose(Borb)

            verbose("Step %s" % 4)
            qorb = len(orb)  # size of orbit
            verbose(qorb)


            verbose("Step %s" % 5)
            epsorb = prod([F.epsilon(C) for C in orb])
            verbose(epsorb)

            verbose("Step %s" % "6 + 7 + 8")
            if epsorb == 1:
                ctildeorb = 1
                Torb1 = Torb  # T_i'
            else:
                assert epsorb == -1

                if len(Torb.vertices()) > 2:
                    # A1,i is the set of all leafs whose distance to the nearest
                    # vert of degree ge 3 is odd
                    A1orb = []
                    for b in Borb:
                        d = 0
                        for e in Torb.depth_first_search(b, edges=True):
                            d += Torb.edge_label(*e)
                            if Torb.degree(e[1]) >= 3:
                                break
                        if d % 2 == 1:
                            A1orb.append(b)
                    #A1orb = [b for b in Borb if
                    #         min(Torb.distance(b, d3, by_weight=True)
                    #         for d3 in Torb.degree_ge_three_vertices()) % 2 == 1]
                else:
                    A1orb = []
                    if Torb.edges()[0][2] % 2 == 1:
                        A1orb.append(Torb.vertices()[0])

                verbose(A1orb)
                A0orb = [b for b in Torb.vertices() if b not in A1orb]
                verbose(A0orb)

                # TODO is this right action?
                a0orb = len(orbit_decomposition(F, A0orb, cond=lambda x: len(x) % 2 == 1))
                a1orb = len(orbit_decomposition(F, A1orb, cond=lambda x: len(x) % 2 == 1))
                verbose(a0orb)
                verbose(a1orb)
                if a0orb > 0:
                    ctildeorb = 2**(a0orb - 1)
                else:
                    ctildeorb = gcd(a1orb, 2)
                Torb1, F = Torb.contract_odd_order_subtree(F)
            verbose(ctildeorb)

            verbose("Step %s" % 9)
            Borb1 = Torb1.blue_subgraph()

            verbose("Step %s" % 10)
            Fq = lambda inp: reduce(lambda x,y: F(x), [inp] + qorb*[0])
            Qorb = prod(len(fo) for fo in orbit_decomposition(Fq, Borb1))
            verbose(Qorb)

            verbose("Step %s" % 11)
            Torb2 = Torb1.quotient(Fq)  # TODO paper imprecise here perhaps
            # Borb2 = Borb1.quotient(Fq)
            verbose(Torb2)
            verbose(Torb2.edges())

            verbose("Step %s" % 12)
            Borb2 = Torb2.blue_subgraph()
            verbose(Borb2)

            verbose("Step %s" % 13)
            rorb = len(Borb2) - 1
            verbose(rorb)

            verbose("Step %s" % 14)
            su = 0
            for es in Torb2.multiway_cuts(Borb2.vertices()):
                su += prod(e[2] for e in es)
            verbose(su)
            C_Torb = su * Qorb * ctildeorb
            verbose(C_Torb)

            ans *= C_Torb

        return ans


class BYTreeIsomorphism(SageObject):
    r"""
    Isomorphisms between BY-trees, these are graph isomorphisms that preserve
    the BY-tree structure, and additionally assign an sign to each yellow
    component of the tree.

    EXAMPLES::

        sage: from sage_cluster_pictures.cluster_pictures import BYTree, BYTreeIsomorphism
        sage: T = BYTree()
        sage: T.add_blue_vertex('v1', 1)
        sage: T.add_blue_vertex('v2', 0)
        sage: T.add_yellow_edge(('v1', 'v2', 2))
        sage: f = lambda v: {'v1':'v2','v2':'v1'}[v]
        sage: eps = lambda c: -1
        sage: F = BYTreeIsomorphism(T, T, f, eps)
        sage: F
        BY-tree isomorphism from BY-tree with 0 yellow vertices, 2 blue vertices, 1 yellow edges, 0 blue edges to BY-tree with 0 yellow vertices, 2 blue vertices, 1 yellow edges, 0 blue edges


    """

    def __init__(self, A, B, f, eps):
        r"""
        See :class:`BYTree` for documentation.

        INPUT:

        - ``A``, ``B`` - BY-trees
        - ``f`` - a function from vertices of ``A`` to vertices of ``B``,
                assumed to be bijective, preserve the colouring and genera, and
                that the induced map on edges preserves colouring. 
        - ``eps`` - a function from yellow components of ``A`` to `\{\pm1\}`.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree, BYTreeIsomorphism
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 0)
            sage: T.add_yellow_edge(('v1', 'v2', 2))
            sage: f = lambda v: {'v1':'v2','v2':'v1'}[v]
            sage: eps = lambda c: -1
            sage: F = BYTreeIsomorphism(T, T, f, eps)
            sage: F
            BY-tree isomorphism from BY-tree with 0 yellow vertices, 2 blue vertices, 1 yellow edges, 0 blue edges to BY-tree with 0 yellow vertices, 2 blue vertices, 1 yellow edges, 0 blue edges
        """
        self._domain = A
        self._codomain = B
        self._f = f
        self._epsilon = eps

    def domain(self):
        r"""
        Return the domain of ``self``.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree, BYTreeIsomorphism
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 0)
            sage: T.add_yellow_edge(('v1', 'v2', 2))
            sage: f = lambda v: {'v1':'v2','v2':'v1'}[v]
            sage: eps = lambda c: -1
            sage: F = BYTreeIsomorphism(T, T, f, eps)
            sage: F.domain()
            BY-tree with 0 yellow vertices, 2 blue vertices, 1 yellow edges, 0 blue edges
        """
        return self._domain

    def codomain(self):
        r"""
        Return the codomain of ``self``.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree, BYTreeIsomorphism
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 0)
            sage: T.add_yellow_edge(('v1', 'v2', 2))
            sage: f = lambda v: {'v1':'v2','v2':'v1'}[v]
            sage: eps = lambda c: -1
            sage: F = BYTreeIsomorphism(T, T, f, eps)
            sage: F.codomain()
            BY-tree with 0 yellow vertices, 2 blue vertices, 1 yellow edges, 0 blue edges
        """
        return self._codomain

    def epsilon(self, inp):
        r"""
        Evaluate the sign function `\epsilon` associated to ``self`` at
        the component ``inp``.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree, BYTreeIsomorphism
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 0)
            sage: T.add_yellow_edge(('v1', 'v2', 2))
            sage: f = lambda v: {'v1':'v2','v2':'v1'}[v]
            sage: eps = lambda c: -1
            sage: F = BYTreeIsomorphism(T, T, f, eps)
            sage: F.epsilon(T.edges())
            -1
        """
        return self._epsilon(inp)

    def __call__(self, inp):
        r"""
        Return the image of the vertex or edge under ``self``.

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree, BYTreeIsomorphism
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 0)
            sage: T.add_yellow_edge(('v1', 'v2', 2))
            sage: f = lambda v: {'v1':'v2','v2':'v1'}[v]
            sage: eps = lambda c: -1
            sage: F = BYTreeIsomorphism(T, T, f, eps)
            sage: F('v2')
            'v1'
            sage: F('v1')
            'v2'
            sage: F(T.edges()[0])
            ('v2', 'v1', 2)
        """
        if isinstance(inp, tuple):
            return (self._f(inp[0]), self._f(inp[1]), inp[2])
        return self._f(inp)

    # TODO this looks a bit silly at present because the BY-trees will have the same repr.
    def _repr_(self):
        r"""
        Return a string representation of ``self``.

        OUTPUT:

        - a string

        EXAMPLES::

            sage: from sage_cluster_pictures.cluster_pictures import BYTree, BYTreeIsomorphism
            sage: T = BYTree()
            sage: T.add_blue_vertex('v1', 1)
            sage: T.add_blue_vertex('v2', 0)
            sage: T.add_yellow_edge(('v1', 'v2', 2))
            sage: f = lambda v: {'v1':'v2','v2':'v1'}[v]
            sage: eps = lambda c: -1
            sage: F = BYTreeIsomorphism(T, T, f, eps)
            sage: F
            BY-tree isomorphism from BY-tree with 0 yellow vertices, 2 blue vertices, 1 yellow edges, 0 blue edges to BY-tree with 0 yellow vertices, 2 blue vertices, 1 yellow edges, 0 blue edges
        """
        return "BY-tree isomorphism from %s to %s" % (self.domain(), self.codomain())

    def _test(self):
        r"""
        Check that ``self`` satisfies the properties assumed of it.
        """
        return True

