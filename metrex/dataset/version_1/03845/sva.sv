// SVA for decoder_3to8
module decoder_3to8_sva (input logic A, B, C, input logic [7:0] Y);
  default clocking cb @(A or B or C or Y); endclocking

  // Known inputs decode to one-hot with zero-cycle latency
  assert property (@(A or B or C)
                   !$isunknown({A,B,C}) |-> ##0 (Y == (8'b1 << {A,B,C})))
    else $error("Decode mismatch: ABC=%b Y=%b", {A,B,C}, Y);

  // Any X/Z on inputs forces Y=0 via default case
  assert property (@(A or B or C)
                   $isunknown({A,B,C}) |-> ##0 (Y == 8'b0))
    else $error("Unknown ABC must force Y=0: ABC=%b Y=%b", {A,B,C}, Y);

  // Output is one-hot or all-zero (for X/Z input)
  assert property ($onehot0(Y))
    else $error("Y not onehot0: %b", Y);

  // Combinational: Y only changes when inputs change
  assert property ($changed(Y) |-> $changed({A,B,C}))
    else $error("Y changed without ABC change: ABC=%b Y=%b", {A,B,C}, Y);

  // Coverage: exercise all 8 decode values
  genvar i;
  generate
    for (i=0; i<8; i++) begin : gen_cov
      cover property (@(A or B or C)
                      !$isunknown({A,B,C}) && ({A,B,C} == i[2:0]) ##0 Y[i]);
    end
  endgenerate

  // Coverage: default branch on X/Z inputs
  cover property (@(A or B or C) $isunknown({A,B,C}) ##0 (Y == 8'b0));
endmodule

bind decoder_3to8 decoder_3to8_sva u_decoder_3to8_sva(.A(A), .B(B), .C(C), .Y(Y));