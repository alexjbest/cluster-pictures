=====================================================================================
 sage-numerical-interactive-mip: Interactive mixed integer linear programming solver
=====================================================================================
.. plot::

    from sage_numerical_interactive_mip import InteractiveMILPProblemStandardForm
    A = ([-1, 1], [8, 2])
    b = (2, 17)
    c = (QQ('55/10'), QQ('21/10'))
    P = InteractiveMILPProblemStandardForm(A, b, c, integer_variables=True)
    n, D = P.run_cutting_plane_method(separator="gomory_fractional", revised=True, plot=False, show_steps=False)
    P = InteractiveMILPProblemStandardForm.with_relaxation(D._problem, integer_variables=P.integer_variables())
    g = P.plot(number_of_cuts=n, xmin=-4, xmax=12, ymin=0, ymax=8)
    g.set_legend_options(title="Gomory fractional cutting plane proceedure")
    sphinx_plot(g, figsize=(8,4), aspect_ratio=1)

Project page: https://github.com/mkoeppe/sage-numerical-interactive-mip

.. include:: ../../README.rst
   :start-after: intro

.. include:: ../../THANKS.rst

Modules
=======

.. toctree::
   :maxdepth: 2

   interactive_milp_problem
   solver_dictionaries
