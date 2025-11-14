// SVA for bitwise_operators (clockless, bindable)
// Checks functional correctness, independence, stability; includes concise coverage.

module bitwise_operators_sva
(
  input logic [7:0] in1,
  input logic [7:0] in2,
  input logic [7:0] out_and,
  input logic [7:0] out_or,
  input logic [7:0] out_xor,
  input logic [7:0] out_not
);

  // Functional equivalence (4-state accurate)
  assert property (@(in1 or in2) out_and === (in1 & in2));
  assert property (@(in1 or in2) out_or  === (in1 | in2));
  assert property (@(in1 or in2) out_xor === (in1 ^ in2));
  assert property (@(in1 or in2) out_not === (~in1));

  // No-X propagation when inputs are known
  assert property (@(in1 or in2) !$isunknown({in1,in2}) |-> !$isunknown({out_and,out_or,out_xor,out_not}));

  // Independence: out_not must not depend on in2
  assert property (@(in2) $stable(in1) |-> $stable(out_not));

  // Outputs only change in response to input change (no spurious glitches at sample points)
  assert property (@(out_and or out_or or out_xor or out_not) !$stable({in1,in2}));

  // Useful corner-case identities
  assert property (@(in1 or in2) (in2==8'h00) |-> (out_and==8'h00 && out_or==in1 && out_xor==in1));
  assert property (@(in1 or in2) (in2==8'hFF) |-> (out_and==in1 && out_or==8'hFF && out_xor==~in1));

  // Coverage: key patterns
  cover property (@(in1 or in2) in1==8'h00 && in2==8'h00);
  cover property (@(in1 or in2) in1==8'hFF && in2==8'hFF);
  cover property (@(in1 or in2) in1==8'hAA && in2==8'h55);
  cover property (@(in1 or in2) in1==8'h55 && in2==8'hAA);

  // Coverage: per-bit activity on both inputs
  genvar i;
  generate
    for (i=0;i<8;i++) begin : g_cov_bits
      cover property (@(in1[i]) $rose(in1[i]));
      cover property (@(in1[i]) $fell(in1[i]));
      cover property (@(in2[i]) $rose(in2[i]));
      cover property (@(in2[i]) $fell(in2[i]));
    end
  endgenerate

endmodule

// Bind into the DUT. Adjust instance path or use a global bind as needed.
bind bitwise_operators bitwise_operators_sva
(
  .in1(in1),
  .in2(in2),
  .out_and(out_and),
  .out_or(out_or),
  .out_xor(out_xor),
  .out_not(out_not)
);