=====================================================================================
 sage-cluster-pictures: Cluster pictures in SageMath
=====================================================================================
.. plot::

    from sage_cluster_pictures import *
    K = Qp(7,150)
    x = polygen(K)
    L = K.extension(x^2 + 1, names='a')
    x = polygen(L)
    L2 = L.extension(x^2 - 7, names='b')
    x = polygen(L2)
    H = HyperellipticCurve((x^2+7^2)*(x^2-7^(15))*(x-7^6)*(x-7^6-7^9))
    R = Cluster.from_curve(H)
    g = show(R)
    g.set_legend_options(title="A cluster picture")
    sphinx_plot(g, figsize=(8,4), aspect_ratio=1)

Project page: https://github.com/alexjbest/cluster-pictures

.. include:: ../../README.rst
   :start-after: intro

.. include:: ../../THANKS.rst

Modules
=======

.. toctree::
   :maxdepth: 2

   cluster_pictures
