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

