Interpreting results FAQS
-------------------------

Where do assertions fail
^^^^^^^^^^^^^^^^^^^^^^^^

**Q:** How do I see what is causing my assertion to fail?

**A:** If an assertion is failing, SBY will provide a counterexample trace.
Provided you are not using the ``append`` option, the final cycle in this trace
is the cycle in which the assertion does not hold.  Check out our
:external+sby:doc:`quickstart guide <quickstart>` for a worked example of
examining and fixing a failing assertion.


Witness cover traces
^^^^^^^^^^^^^^^^^^^^

**Q:** How do I produce witness cover traces for a passing assertion?

**A:** Check out the `witness cover section
<https://yosyshq.readthedocs.io/projects/ap120/en/latest/#witness-cover>`_ of
our whitepaper, `Weak precondition cover and witness for SVA properties
<https://yosyshq.readthedocs.io/projects/ap120>`_.


Can liveness properties fail
^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 
**Q:** Is it possible to have liveness property to fail? Or will it just get
stuck in formal run 

**A:** We don't recommend using liveness properties - it's almost always better
to replace with an assertion of something happening within a certain timeframe.

The example our CTO gives is of a design that is stuck in a deadlock, but it has
a 64 bit counter and when that overflows, things start up again. Liveness will
tell you "yup, this design will do things eventually" but it really doesn't help
you because that 64 bit counter is so large that your design will basically
never start again.
