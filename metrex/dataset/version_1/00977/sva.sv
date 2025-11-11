// SVA for module t. Bind this file to the DUT.
// bind t t_sva u_t_sva(.*);

module t_sva (
  input reset,
  input a, b, c, en,
  input o1, o2, o3, o4, o5
);

  // Convenience: trigger on any input edge to evaluate combinational intent
  // Note: ##0 used to sample after delta/NBA updates.
  // Event expression repeated inline for portability.

  // Reset behavior
  assert property (@(posedge reset or negedge reset or posedge en or negedge en
                     or posedge a or negedge a or posedge b or negedge b
                     or posedge c or negedge c)
                   reset |-> ##0 ({o1,o2,o3,o4,o5} == 5'b0));

  // o1
  assert property (@(posedge reset or negedge reset or posedge en or negedge en
                     or posedge a or negedge a or posedge b or negedge b
                     or posedge c or negedge c)
                   !reset |-> ##0 (o1 == 1'b1));

  // o2 (final assignment forces 1 when not in reset)
  assert property (@(posedge reset or negedge reset or posedge en or negedge en
                     or posedge a or negedge a or posedge b or negedge b
                     or posedge c or negedge c)
                   !reset |-> ##0 (o2 == 1'b1));

  // o3
  assert property (@(posedge reset or negedge reset or posedge en or negedge en
                     or posedge a or negedge a or posedge b or negedge b
                     or posedge c or negedge c)
                   (!reset && (en || b)) |-> ##0 (o3 == 1'b1));
  assert property (@(posedge reset or negedge reset or posedge en or negedge en
                     or posedge a or negedge a or posedge b or negedge b
                     or posedge c or negedge c)
                   (!reset && !en && !b) |-> ##0 (o3 == a));

  // o4
  assert property (@(posedge reset or negedge reset or posedge en or negedge en
                     or posedge a or negedge a or posedge b or negedge b
                     or posedge c or negedge c)
                   (!reset && en && c) |-> ##0 (o4 == 1'b1));
  assert property (@(posedge reset or negedge reset or posedge en or negedge en
                     or posedge a or negedge a or posedge b or negedge b
                     or posedge c or negedge c)
                   (!reset && en && !c) |-> ##0 (o4 == ((~a) ^ b)));
  assert property (@(posedge reset or negedge reset or posedge en or negedge en
                     or posedge a or negedge a or posedge b or negedge b
                     or posedge c or negedge c)
                   (!reset && !en) |-> ##0 (o4 == 1'b0));

  // o5 (with hold when !en && !b)
  assert property (@(posedge reset or negedge reset or posedge en or negedge en
                     or posedge a or negedge a or posedge b or negedge b
                     or posedge c or negedge c)
                   (!reset && en) |-> ##0 (o5 == a));
  assert property (@(posedge reset or negedge reset or posedge en or negedge en
                     or posedge a or negedge a or posedge b or negedge b
                     or posedge c or negedge c)
                   (!reset && !en && b) |-> ##0 (o5 == (~b)));
  // Robust 2-sample hold check for latch behavior on o5 when !en && !b
  sequence hold_cond; !reset && !en && !b; endsequence
  assert property (@(posedge reset or negedge reset or posedge en or negedge en
                     or posedge a or negedge a or posedge b or negedge b
                     or posedge c or negedge c)
                   hold_cond ##1 hold_cond |-> (o5 == $past(o5,1)));

  // Sensitivity/functional consistency: if only c changes while en=1, o4 must follow c path immediately.
  // This will flag the missing 'c' in the DUT sensitivity list.
  assert property (@(posedge reset or negedge reset or posedge en or negedge en
                     or posedge a or negedge a or posedge b or negedge b
                     or posedge c or negedge c)
                   (!reset && en && $changed(c) && !$changed({reset,en,a,b}))
                   |-> ##0 (o4 == (c ? 1'b1 : ((~a) ^ b))));

  // Basic X-check (post-update) when not in reset
  assert property (@(posedge reset or negedge reset or posedge en or negedge en
                     or posedge a or negedge a or posedge b or negedge b
                     or posedge c or negedge c)
                   !reset |-> ##0 (!$isunknown({o1,o2,o3,o4,o5})));

  // Coverage: hit all meaningful branches and behaviors
  cover property (@(posedge reset or negedge reset or posedge en or negedge en
                    or posedge a or negedge a or posedge b or negedge b
                    or posedge c or negedge c) reset);
  cover property (@(posedge reset or negedge reset or posedge en or negedge en
                    or posedge a or negedge a or posedge b or negedge b
                    or posedge c or negedge c) !reset && en && a);
  cover property (@(posedge reset or negedge reset or posedge en or negedge en
                    or posedge a or negedge a or posedge b or negedge b
                    or posedge c or negedge c) !reset && en && !a);
  cover property (@(posedge reset or negedge reset or posedge en or negedge en
                    or posedge a or negedge a or posedge b or negedge b
                    or posedge c or negedge c) !reset && en && c);
  cover property (@(posedge reset or negedge reset or posedge en or negedge en
                    or posedge a or negedge a or posedge b or negedge b
                    or posedge c or negedge c) !reset && en && !c);
  cover property (@(posedge reset or negedge reset or posedge en or negedge en
                    or posedge a or negedge a or posedge b or negedge b
                    or posedge c or negedge c) !reset && !en && b);
  cover property (@(posedge reset or negedge reset or posedge en or negedge en
                    or posedge a or negedge a or posedge b or negedge b
                    or posedge c or negedge c) !reset && !en && !b);
  cover property (@(posedge reset or negedge reset or posedge en or negedge en
                    or posedge a or negedge a or posedge b or negedge b
                    or posedge c or negedge c)
                  (!reset && en) ##1 (!reset && en && $changed(c))); // exercise c-dependence of o4
  cover property (@(posedge reset or negedge reset or posedge en or negedge en
                    or posedge a or negedge a or posedge b or negedge b
                    or posedge c or negedge c)
                  hold_cond ##1 hold_cond); // o5 hold case

endmodule