// SVA for decoder_3to8. Bind this module to the DUT.
// Example: bind decoder_3to8 decoder_3to8_sva u_decoder_3to8_sva(.*);

module decoder_3to8_sva (
    input  logic        clk,
    input  logic [2:0]  abc,
    input  logic [7:0]  y
);
  default clocking cb @(posedge clk); endclocking

  // Use $past(1'b1) as a "past-valid" guard to skip the first cycle.
  // Functional correctness: y equals one-hot(abc) computed at the same edge.
  assert property ( $past(1'b1) |-> ( y == (8'h1 << $past(abc)) ) );

  // Output is strictly one-hot (never 0/multi-bit).
  assert property ( $past(1'b1) |-> $onehot(y) );

  // No X/Z on key signals after the first cycle.
  assert property ( $past(1'b1) |-> !$isunknown({abc, y}) );

  // Functional coverage: see each code point exercised and correctly decoded.
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : g_cov_map
      cover property ( $past(1'b1) && ($past(abc) == i) && (y == (8'h1 << i)) );
    end
  endgenerate
endmodule