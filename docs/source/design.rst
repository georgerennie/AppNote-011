Design setup FAQs
-----------------

.. Includes/defines
.. ^^^^^^^^^^^^^^^^

.. TODO


.. SVA+VHDL
.. ^^^^^^^^

.. pending https://github.com/YosysHQ/sby/pull/264


SystemVerilog Assertions (SVA)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

**Q:** What subset of SVA is supported?

**A:** Refer to the SBY docs: :external+sby:ref:`supported sva property syntax`.


Blackboxing
^^^^^^^^^^^

**Q:** How do I blackbox a submodule to make SBY run faster?  I tried to use the
:external+yosys:doc:`blackbox command <cmd/blackbox>` but then it raises an
error. 

**A:** Many of the Yosys commands needed for SBY do not support blackbox
modules.  However, it is possible to use the :external+yosys:doc:`cutpoint
command <cmd/cutpoint>` to disconnect a module's inputs and drive its outputs
with ``$anyseq`` cells which the solver can assign any value to at each step.
This then allows the module to be verified independently of the rest of the
design.

**Q:** Is it possible to blackbox all multipliers in a design?

**A:** Yes!  Calling ``cutpoint t:$mul`` after loading the design will add
cutpoints for all cells of type ``$mul``, i.e. all of the mutlipliers.
