// SVA for priority_encoder
// Bind into the DUT; no DUT edits required.

module priority_encoder_sva (
  input logic [2:0] in,
  input logic [7:0] out
);
  default clocking cb @(*); endclocking

  // Exact functional equivalence for known inputs
  ap_eq:       assert property (disable iff ($isunknown(in)) out === (8'b1 << in));

  // X/Z input maps to zero
  ap_x_to_zero: assert property ($isunknown(in) |-> out === 8'b0);

  // Output is never multi-hot (allows zero when input is unknown)
  ap_onehot0:  assert property ($onehot0(out));

  // Zero output only when input is X/Z (no valid input produces zero)
  ap_zero_implies_x: assert property (out === 8'b0 |-> $isunknown(in));

  // Functional coverage: hit every decode
  genvar i;
  generate
    for (i=0; i<8; i++) begin : COV
      cover property (in == i && out === (8'b1 << i));
    end
  endgenerate
endmodule

bind priority_encoder priority_encoder_sva sva (.in(in), .out(out));