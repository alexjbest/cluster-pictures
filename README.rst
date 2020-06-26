=====================================================================================
Cluster pictures
=====================================================================================

.. image:: https://github.com/alexjbest/cluster-pictures/workflows/Build%20and%20test%20Python%20package/badge.svg
   :alt: [Build and test Python package]
   :target: https://github.com/alexjbest/cluster-pictures/actions/

.. image:: https://mybinder.org/badge_logo.svg
 :target: https://mybinder.org/v2/gh/alexjbest/cluster-pictures/master?filepath=notebooks%2Fdemo.ipynb


.. intro

This package implements the machinery of cluster pictures, starting with work of Maistret, Morgan, Dokchitser and Dokchitser, in Sage.

It was written by Alex J. Best and Raymond van Bommel.

The work of, and help from, A. Betts, M. Bisatt, V. Dokchitser, O. Faraggi, S. Kunzweiler, C. Maistret, A.Morgan, S. Muselli, and S. Nowell were invaluable in the writing of this package.

This work was supported by a grant from the Simons Foundation (546235) for the collaboration "Arithmetic Geometry, Number Theory, and Computation", through a workshop held at ICERM. 

As a template for the project structure: https://github.com/mkoeppe/sage-numerical-interactive-mip was a great help.

How to install
==============

You can try out this package in an online notebook environment without installing thanks to MyBinder, just click the launch binder icon above.

If you have SageMath installed (version 9.1 or higher recommended) installation should be possible via pip, for example with:

.. code-block:: shell-session

    sage -pip install --user git+https://github.com/alexjbest/cluster-pictures

This needs a working SageMath; install, for example, from conda-forge as
described in http://doc.sagemath.org/html/en/installation/conda.html

The code comes with extensive documentation and tests; see the
docstrings in the modules or online at https://alexjbest.github.io/cluster-pictures/.

How to run the testsuite and build the HTML documentation
=========================================================

Install ``tox``, make sure that ``sage`` is accessible in your ``PATH``
and then run ``tox``.

This also builds the documentation in ``.tox/docs/tmp/html/index.html``.
