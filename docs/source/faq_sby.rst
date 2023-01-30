FAQs relating to SBY
--------------------

Semantics of "disable iff"
^^^^^^^^^^^^^^^^^^^^^^^^^^

**Q:** I would have expected the following to pass. Why does it not pass?

.. code-block:: systemverilog

   assume property (@(posedge clock) A |-> B disable iff (reset));
   assert property (@(posedge clock) A && !reset |-> B );

**A:** Both of those properties are two simulation cycles long, because the
clock edge between those two cycles is part of the property. The ``disable iff``
statement behaves similar to an *asynchronous* reset that is not sampled
by the clock, thus the sequence ``A && !B && !reset ##1 reset`` will disable
the assumption, but will not disable the assertion in the above example.

Choosing an engine and solver
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

**Q:** How do I know which formal engine and/or which solver to use for
verifying my design?

**A:** Different combinations of engine and solver will perform differently and
may support different features or functionalities.  The `SBY engines reference
<https://yosyshq.readthedocs.io/projects/sby/en/latest/reference.html#engines-section>`_
lists all currently supported engines, their options, available solvers, and
which modes they operate in.  At this time, a comprehensive comparison of when
to use different engines/solvers is not yet available.

With the introduction of the ``--autotune`` option it is now possible to
automatically compare available engines for a given SBY task.  Autotune will run
each engine, providing a report of time taken and the status returned.  This can
be used to quickly determine the fastest configuration while continuing to
iterate on a design. Check out the `autotune docs
<https://yosyshq.readthedocs.io/projects/sby/en/latest/autotune.html>`_ for more
information.

Witness cover traces
^^^^^^^^^^^^^^^^^^^^

**Q:** How do I produce witness cover traces for a passing assertion?

**A:** Check out the `witness cover section
<https://yosyshq.readthedocs.io/projects/ap120/en/latest/#witness-cover>`_ of our
whitepaper, `Weak precondition cover and witness for SVA properties
<https://yosyshq.readthedocs.io/projects/ap120>`_.

Where do assertions fail
^^^^^^^^^^^^^^^^^^^^^^^^

**Q:** How do I see what is causing my assertion to fail?

**A:** If an assertion is failing, SBY will provide a counterexample trace.
Provided you are not using the ``append`` option, the final cycle in this trace
is the cycle in which the assertion does not hold.  Check out our `quickstart
guide <https://yosyshq.readthedocs.io/projects/sby/en/latest/quickstart.html>`_
for a worked example of examining and fixing a failing assertion.
