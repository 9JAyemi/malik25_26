// SVA checker for binary_decoder_3to8
// Bind this to the DUT and drive clk from a free-running TB clock.

module binary_decoder_3to8_sva (
  input logic              clk,
  input logic [2:0]        in,
  input logic [7:0]        out
);
  default clocking cb @(posedge clk); endclocking

  // Known input must decode to exact one-hot
  assert property ( !$isunknown(in) |=> (out == (8'b0000_0001 << in) && $onehot(out)) )
    else $error("Decode mismatch for known input: in=%0d out=%0h", in, out);

  // Unknown input must drive out to all zeros and known
  assert property ( $isunknown(in) |=> (out == 8'h00 && !$isunknown(out)) )
    else $error("Out not zero/known for unknown input: in=%b out=%0h", in, out);

  // Sanity: out is always onehot0 (zero or exactly one bit set, no X/Z)
  assert property ( $onehot0(out) )
    else $error("Out not onehot0: out=%0h", out);

  // Functional coverage: hit all 8 decode points
  generate
    genvar i;
    for (i = 0; i < 8; i++) begin : CODES
      cover property ( (!$isunknown(in) && in == i) |=> (out == (8'b0000_0001 << i) && out[i]) );
    end
  endgenerate

  // Coverage for unknown input path
  cover property ( $isunknown(in) |=> out == 8'h00 );

endmodule

// Example bind (instantiate in your TB; provide a sampling clock):
// bind binary_decoder_3to8 binary_decoder_3to8_sva u_bin_dec_sva (.clk(tb_clk), .in(in), .out(out));