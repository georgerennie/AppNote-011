Unexpected behaviour FAQs
-------------------------

Design initialisation
^^^^^^^^^^^^^^^^^^^^^

**Q:** Why does my design not get reset properly at the start?

**A:** SBY does not consider reset signals special. If you want to restrict your proof to only
certain behaviors of the reset signal, add an ``assume()`` statement enforcing the reset sequence,
e.g. ``initial assume(reset);`` (Yosys also adds the non-standard ``$initstate`` for use in
conditionals, e.g. assume property (``@(posedge clk) $initstate |-> reset [*3]);``).

Where possible we encourage writing your properties in such a way as to be able to leave the reset
signal unconstrained after the initial cycles, so as to check for bugs that might occur after a soft
reset.


Clock signals
^^^^^^^^^^^^^

**Q:** How does SBY detect and handle clock signals?

**A:** How SBY treats the clock signals differs depending on if you are using multi-clock mode
(``multiclock on`` in the ``[options]`` section) or not. In single-clock mode, the clock signal's
actual value is disregarded, we assume all registered signals update simultaneously, and the solver
has one variable per signal per clock cycle to determine. So internally, the solver will actually
never see the clock change, and we artificially add the toggling of the clock signal when generating
the trace - but that can lead to some discrepancies if there are any signals that are assigned the
value of the clock signal (such as with submodules).

In multiclock mode, the clock signal is instead treated as a regular input, and the solver can
freely choose whether to toggle it, unless you add assumptions. This means that the clock signal
will not obey the implicit rules of clock signals like having a consistent period or duty cycle, but
while surprising at first, this is actually not a disadvantage most of the time - when the clocks
are not related, it's almost always possible to eventually reach a specific interleaving of clock
edges if you let the system run long enough. Not having those constraints in place means that the
solver can find the worst case in only a few steps, giving you a short trace. With the constraints,
getting to that point might take so long that the problem becomes computationally intractable. If
your clocks are actually related, do add an assumption about that.


**Q:** When do I need to enable multi-clock mode?

**A:** You need to set ``multiclock on`` in the ``[options]`` section whenver the design contains entities that are sensitive to different events.
This includes:

- multiple clock signals
- multiple edges of the same clock signal
- any asynchronous logic (with the exception of asynchronous resets that should be treated as synchronous)


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
