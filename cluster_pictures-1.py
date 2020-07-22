from sage_cluster_pictures.cluster_pictures import *
K = Qp(3,200)
x = polygen(K)
H = HyperellipticCurve(x**6 + 2*x**3 + 4*x**2 + 4*x + 1)
R = Cluster.from_curve(H)
R.BY_tree().plot()