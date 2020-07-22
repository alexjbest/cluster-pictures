from sage_cluster_pictures.cluster_pictures import Cluster
p = 5
x = polygen(Qp(p,150))
H = HyperellipticCurve(x*(x-p)*(x-2*p)*(x-3*p)*(x-1)*(x-2)*(x-3)*(x-4))
R = Cluster.from_curve(H)
R.dual_graph()