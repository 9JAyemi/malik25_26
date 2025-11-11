// SVA checker for my_module
// Focus: concise, high-quality functional checking and essential coverage.
// Bind this checker to my_module to verify both ports and key internal nets.

module my_module_sva (
  input logic a, b, c,
  input logic out1, out2,
  input logic b_and_c, b_xor_c
);

  // Combinational functional correctness (and no X/Z when inputs are known)
  always_comb begin
    assert (b_and_c === (b & c)) else $error("b_and_c != b & c");
    assert (b_xor_c === (b ^ c)) else $error("b_xor_c != b ^ c");
    assert (out1 === ((a == 1'b1) ? b_and_c : b_xor_c)) else $error("out1 mismatch");
    assert (out2 === (a ^ c)) else $error("out2 mismatch");
    if (!$isunknown({a,b,c})) assert (!$isunknown({out1,out2,b_and_c,b_xor_c}))
      else $error("X/Z on outputs with known inputs");
  end

  // Independence checks
  // out2 must not depend on b
  property p_out2_indep_b;
    @(posedge b or negedge b) $stable({a,c}) |-> $stable(out2);
  endproperty
  assert property (p_out2_indep_b);

  // Internal nets must not depend on a
  property p_internals_indep_a;
    @(posedge a or negedge a) $stable({b,c}) |-> ($stable(b_and_c) && $stable(b_xor_c));
  endproperty
  assert property (p_internals_indep_a);

  // Minimal but meaningful coverage
  // Cover both out1 branches taken at least once
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
                  (a && (out1 === b_and_c)));
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c)
                  (!a && (out1 === b_xor_c)));

  // Exercise internal ops and out2 both 0 and 1
  cover property (@(posedge b or negedge b or posedge c or negedge c) b_and_c);
  cover property (@(posedge b or negedge b or posedge c or negedge c) b_xor_c);
  cover property (@(posedge a or negedge a or posedge c or negedge c) out2);
  cover property (@(posedge a or negedge a or posedge c or negedge c) !out2);

  // Output toggling coverage (sanity)
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge c or negedge c) $changed(out1));
  cover property (@(posedge a or negedge a or posedge c or negedge c) $changed(out2));

endmodule

// Bind into DUT (accessing internals)
bind my_module my_module_sva u_my_module_sva (
  .a(a), .b(b), .c(c),
  .out1(out1), .out2(out2),
  .b_and_c(b_and_c), .b_xor_c(b_xor_c)
);