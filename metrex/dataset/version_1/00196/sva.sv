// SVA checker for LSHIFTER_32bit
module LSHIFTER_32bit_sva (
  input  logic        C,
  input  logic [31:0] D,
  input  logic [31:0] S,
  input  logic        C1,
  input  logic [30:0] shifted
);

  // Interface-level functionality
  ap_pass:  assert property (@(*) (C===1'b1) |-> (S===D));
  ap_shift: assert property (@(*) (C===1'b0) |-> (S=== {D[30:0], 1'b0}));

  // Internal relations
  ap_c1:        assert property (@(*) (C1 === ~C));
  ap_shift_def: assert property (@(*) (shifted === {D[29:0], 1'b0}));

  // X-propagation: known inputs imply known output
  ap_known: assert property (@(*) (!$isunknown({C,D})) |-> !$isunknown(S));

  // Functional coverage
  cp_pass:  cover property (@(*) (C===1'b1 && S===D));
  cp_shift: cover property (@(*) (C===1'b0 && S=== {D[30:0], 1'b0}));
  cp_msb:   cover property (@(*) (C===1'b0 && D[30]===1'b1 && S[31]===1'b1));

endmodule

// Bind into DUT (allows access to internals C1 and shifted)
bind LSHIFTER_32bit LSHIFTER_32bit_sva u_lshifter_32bit_sva (
  .C(C),
  .D(D),
  .S(S),
  .C1(C1),
  .shifted(shifted)
);