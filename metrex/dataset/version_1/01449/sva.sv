// SVA checker for xor_module
// Concise, high-quality assertions and coverage for combinational XOR with parameter C.

module xor_module_sva #(parameter logic [3:0] C = 4'hB)
(
  input logic [3:0] a,
  input logic [3:0] b
);

  // Immediate combinational check (strongest for zero-delay continuous assign)
  always_comb
    assert (b === (a ^ C))
      else $error("xor_module: b=%0h != a^C=%0h (a=%0h C=%0h)", b, (a ^ C), a, C);

  // Concurrent assertion sampled on any a/b activity
  property p_xor_relation;
    @(a or b) b === (a ^ C);
  endproperty
  assert property (p_xor_relation);

  // If a is fully known, b must be fully known (no unintended X/Z on output)
  property p_no_x_when_a_known;
    @(a or b) (!$isunknown(a)) |-> (!$isunknown(b));
  endproperty
  assert property (p_no_x_when_a_known);

  // Functional coverage: hit all input values with correct corresponding output
  genvar v;
  generate
    for (v = 0; v < 16; v++) begin : gen_cov_all
      cover property (@(a)) (a === v[3:0]) && (b === ((v[3:0]) ^ C));
    end
  endgenerate

endmodule

// Bind the checker to all instances of xor_module, passing the DUT's parameter c
bind xor_module xor_module_sva #(.C(c)) xor_module_sva_i (.a(a), .b(b));