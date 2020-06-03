=====================================================================================
Cluster pictures
=====================================================================================

.. image:: https://github.com/alexjbest/cluster-pictures/workflows/Build%20and%20test%20Python%20package/badge.svg
   :alt: [Build and test Python package]
   :target: https://github.com/alexjbest/cluster-pictures/actions/


.. intro

This package implements the machinery of cluster pictures of Maistret, Morgan, Dokchitser and Dokchitser in Sage.

It was written by Alex J. Best and Raymond van Bommel.

This project used as a template https://github.com/mkoeppe/sage-numerical-interactive-mip.

How to use
==========

This needs a working SageMath; install, for example, from conda-forge as
described in http://doc.sagemath.org/html/en/installation/conda.html

The code comes with extensive documentation and tests; see the
docstrings in the modules or online at https://alexjbest.github.io/cluster-pictures/.

How to run the testsuite and build the HTML documentation
=========================================================

Install ``tox``, make sure that ``sage`` is accessible in your ``PATH``
and then run ``tox``.

This also builds the documentation in ``.tox/docs/tmp/html/index.html``.
