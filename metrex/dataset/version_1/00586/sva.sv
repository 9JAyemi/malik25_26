// SVA for decoder_4_to_16
// Binds to DUT; checks functional mapping, one-hot, X-safety, and provides concise coverage.

module decoder_4_to_16_sva (decoder_4_to_16 dut);
  wire [1:0]  AB = dut.AB;
  wire [15:0] Y  = dut.Y;

  // X/Z safety on interface
  assert property (@(*) !$isunknown(AB));
  assert property (@(*) !$isunknown(Y));

  // Functional correctness: one-hot at position AB (zero-extended)
  assert property (@(*) Y == (16'h0001 << AB));

  // One-hot guarantee
  assert property (@(*) $onehot(Y));

  // Unreachable high outputs must remain zero
  assert property (@(*) Y[15:4] == '0);

  // Functional coverage: all decodes exercised
  cover property (@(*) (AB==2'd0 && Y==16'h0001));
  cover property (@(*) (AB==2'd1 && Y==16'h0002));
  cover property (@(*) (AB==2'd2 && Y==16'h0004));
  cover property (@(*) (AB==2'd3 && Y==16'h0008));
endmodule

bind decoder_4_to_16 decoder_4_to_16_sva sva_inst();