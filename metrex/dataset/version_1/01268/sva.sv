// SVA checker for decoder_3to8_case
module decoder_3to8_case_sva (
    input logic clk,
    input logic A, B, C,
    input logic [7:0] Y
);
  default clocking cb @(posedge clk); endclocking

  // Assumptions: inputs must be 0/1 (no X/Z) to avoid latchy behavior on X in case
  assume property (!$isunknown({A,B,C}));

  // Correct decode and sanity
  assert property (Y == (8'b00000001 << {A,B,C}));
  assert property ($onehot(Y));
  assert property (!$isunknown(Y));

  // Stability: if inputs don't change, outputs don't change
  assert property ($stable({A,B,C}) |-> $stable(Y));

  // Functional coverage: hit all 8 input/output mappings
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : COV
      cover property ( ({A,B,C} == i[2:0]) && (Y == (8'b00000001 << i)) );
    end
  endgenerate
endmodule

// Example bind (connect an appropriate clk from your TB):
// bind decoder_3to8_case decoder_3to8_case_sva u_dec_sva(.clk(tb_clk), .A(A), .B(B), .C(C), .Y(Y));