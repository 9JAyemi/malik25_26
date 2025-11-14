// SVA checker for xor3. Bind this to the DUT.
// Focus: functional equivalence, internal signal correctness, X-prop, and concise coverage.

module xor3_sva;

  // Disable assertions when inputs are X/Z
  default disable iff ($isunknown({a,b,c}));

  // Shorthand clocking event: fire on any input edge
  // (repeat inline for tool compatibility)
  // Event used: @(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)

  // Functional spec: x == (a ^ c) & ~b
  a_func: assert property (@(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
                           1'b1 |-> ##0 (x == ((a ^ c) & ~b)));

  // Structural correctness of internal nets (allow ##0 for delta-cycle settle)
  a_not_a:  assert property (@(posedge a or negedge a) ##0 (not_a   == ~a));
  a_not_b:  assert property (@(posedge b or negedge b) ##0 (not_b   == ~b));
  a_not_c:  assert property (@(posedge c or negedge c) ##0 (not_c   == ~c));

  a_ab:     assert property (@(posedge a or negedge a or posedge b or negedge b) ##0 (a_and_b == (a & b)));
  a_bc:     assert property (@(posedge b or negedge b or posedge c or negedge c) ##0 (b_and_c == (b & c)));
  a_ca:     assert property (@(posedge a or negedge a or posedge c or negedge c) ##0 (c_and_a == (c & a)));

  a_xor1:   assert property (@(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
                             ##0 (xor1 == (not_a ^ b_and_c)));
  a_xor2:   assert property (@(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
                             ##0 (xor2 == (a_and_b ^ not_c)));
  a_x_str:  assert property (@(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
                             ##0 (x == (xor1 ^ xor2)));

  // Known-value check for all internal nodes and output when inputs are known
  a_no_x:   assert property (@(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
                             ##0 !$isunknown({not_a,not_b,not_c,a_and_b,b_and_c,c_and_a,xor1,xor2,x}));

  // Useful behavior corollaries from the spec (catch subtle issues)
  a_eqc_zero:  assert property (@(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
                                (a==c) |-> ##0 (x==1'b0));
  a_axc_b0:    assert property (@(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
                                ((a^c) && !b) |-> ##0 (x==1'b1));
  a_axc_b1:    assert property (@(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
                                ((a^c) &&  b) |-> ##0 (x==1'b0));

  // Concise functional coverage:
  // - All 8 input combinations
  // - Cross with x to ensure truth-table correctness is exercised
  covergroup cg_inputs @(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c);
    coverpoint {a,b,c} iff (!$isunknown({a,b,c})) { bins all[] = {[0:7]}; }
    coverpoint x        iff (!$isunknown({a,b,c}));
    cross {a,b,c}, x;
  endgroup
  cg_inputs cg = new();

  // Cover the functional equivalence firing (sanity)
  c_func: cover property (@(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
                          ##0 (x == ((a ^ c) & ~b)));

endmodule

bind xor3 xor3_sva i_xor3_sva();