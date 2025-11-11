// SVA for bitwise_and
// Quality-focused, concise checks and coverage

`ifndef BITWISE_AND_SVA_SV
`define BITWISE_AND_SVA_SV

module bitwise_and_sva #(parameter int bits = 16)
(
  input logic [bits-1:0] a, b, q
);

  // Functional correctness (guard X/Z to avoid false failures)
  property p_and_correct;
    @(a or b or q) disable iff ($isunknown({a,b,q}))
      q == (a & b);
  endproperty
  assert property (p_and_correct)
    else $error("AND mismatch: q != a & b");

  // No X/Z on q when inputs are known
  property p_no_x_on_q_when_inputs_known;
    @(a or b or q) (!$isunknown({a,b})) |-> (!$isunknown(q));
  endproperty
  assert property (p_no_x_on_q_when_inputs_known)
    else $error("q has X/Z while a,b are known");

  // Per-bit functional activity coverage
  genvar i;
  generate
    for (i = 0; i < bits; i++) begin : cov_bits
      // Observe a case where q[i] == 1 (both inputs 1)
      cover property (@(a or b) a[i] && b[i] && q[i]);
      // Output bit toggles
      cover property (@(a or b or q) $rose(q[i]));
      cover property (@(a or b or q) $fell(q[i]));
    end
  endgenerate

  // Corner cases
  cover property (@(a or b) (a == '0 && b == '0 && q == '0));
  cover property (@(a or b) (a == '1 && b == '1 && q == '1));
  cover property (@(a or b) (a == '1 && b == '0 && q == '0));
  cover property (@(a or b) (a == '0 && b == '1 && q == '0));

endmodule

// Bind into DUT
bind bitwise_and bitwise_and_sva #(.bits(bits)) bitwise_and_sva_i (.a(a), .b(b), .q(q));

`endif