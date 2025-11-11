// SVA checker for decoder_4to16: concise, full functional checks and coverage
module decoder_4to16_sva (
  input logic A, B, C, D,
  input logic [15:0] Y
);

  // Sample on any input change; check after a delta (##0) for settle
  event comb_ev;
  always @(A or B or C or D) -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  logic [3:0]   idx;
  logic [15:0]  expected;
  assign idx      = {A,B,C,D};
  assign expected = ~(16'h1 << idx);

  // Inputs must be known 0/1
  assert property ( !$isunknown({A,B,C,D}) )
    else $error("decoder_4to16: X/Z on inputs A=%b B=%b C=%b D=%b", A,B,C,D);

  // When inputs are known, output must settle next delta to correct one-cold code
  assert property ( disable iff ($isunknown({A,B,C,D})) 1'b1 |-> ##0 (Y === expected) )
    else $error("decoder_4to16: decode mismatch idx=%0d Y=%h exp=%h", idx, Y, expected);

  // Active-low one-hot (one-cold) check and no X/Z on output (when inputs known)
  assert property ( disable iff ($isunknown({A,B,C,D})) 1'b1 |-> ##0 $onehot(~Y) )
    else $error("decoder_4to16: Y not one-cold, Y=%h", Y);

  assert property ( disable iff ($isunknown({A,B,C,D})) 1'b1 |-> ##0 !$isunknown(Y) )
    else $error("decoder_4to16: Y has X/Z, Y=%h", Y);

  // Functional coverage: hit all 16 addresses with correct decode
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : COV
      cover property ( (idx == i) ##0 (Y === ~(16'h1 << i)) );
    end
  endgenerate

endmodule

// Bind into the DUT
bind decoder_4to16 decoder_4to16_sva u_decoder_4to16_sva (.A(A), .B(B), .C(C), .D(D), .Y(Y));