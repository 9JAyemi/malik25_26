// SVA for decoder — concise, high-quality checks and coverage
module decoder_sva (
  input  logic        sel1,
  input  logic        sel0,
  input  logic [15:0] out
);

  // Expected output vector for each input combination
  function automatic logic [15:0] exp_vec (input logic s1, input logic s0);
    unique case ({s1,s0})
      2'b00: exp_vec = 16'b0000_0000_0001_0001; // bits 4,0
      2'b01: exp_vec = 16'b0000_0000_0100_0010; // bits 6,1
      2'b10: exp_vec = 16'b0100_0010_0000_0100; // bits 14,9,2
      2'b11: exp_vec = 16'b1000_1000_0000_1000; // bits 15,11,3
      default: exp_vec = 'x;
    endcase
  endfunction

  // Functional equivalence (full bus check), gated off unknown inputs
  assert property (disable iff ($isunknown({sel1,sel0})) @(*)
                   (out === exp_vec(sel1,sel0)))
    else $error("decoder: out mismatch for sel1=%0b sel0=%0b", sel1, sel0);

  // Base 2->4 decode must be one-hot
  assert property (disable iff ($isunknown({sel1,sel0})) @(*)
                   $onehot(out[3:0]));

  // No X/Z on outputs when inputs are known
  assert property (@(*) (!$isunknown({sel1,sel0})) |-> (!$isunknown(out)));

  // Bits that must always be 0 (concise mask: 5,7,8,10,12,13)
  assert property (@(*) ((out & 16'b0011_0101_1010_0000) == 16'b0));

  // Coverage: all input combinations produce the expected pattern
  cover property (@(*) (! $isunknown({sel1,sel0}) && {sel1,sel0}==2'b00 &&
                        out===exp_vec(sel1,sel0)));
  cover property (@(*) (! $isunknown({sel1,sel0}) && {sel1,sel0}==2'b01 &&
                        out===exp_vec(sel1,sel0)));
  cover property (@(*) (! $isunknown({sel1,sel0}) && {sel1,sel0}==2'b10 &&
                        out===exp_vec(sel1,sel0)));
  cover property (@(*) (! $isunknown({sel1,sel0}) && {sel1,sel0}==2'b11 &&
                        out===exp_vec(sel1,sel0)));

endmodule

// Bind into DUT
bind decoder decoder_sva sva(.sel1(sel1), .sel0(sel0), .out(out));