// decoder_3to8 SVA: bindable, concise, full functional checks and coverage

module decoder_3to8_sva (
  input logic [2:0] in,
  input logic [7:0] out
);

  // Sanity: no X/Z on interface
  always_comb begin
    assert (!$isunknown(in)) else $error("decoder_3to8: 'in' has X/Z (%b)", in);
    assert (!$isunknown(out)) else $error("decoder_3to8: 'out' has X/Z (%b), in=%0d", out, in);
  end

  // Functional: decode equals 1<<in in same delta; out is one-hot; selected bit set
  always_comb begin
    assert (#0 out == (8'b0000_0001 << in))
      else $error("decoder_3to8: mismatch: in=%0d out=%b exp=%b", in, out, (8'b0000_0001 << in));
    assert ($onehot(out))
      else $error("decoder_3to8: out not one-hot: in=%0d out=%b", in, out);
    assert (out[in])
      else $error("decoder_3to8: selected bit not set: in=%0d out=%b", in, out);
  end

  // Coverage: hit all inputs, outputs, and correct mappings
  genvar gi;
  generate
    for (gi = 0; gi < 8; gi++) begin : g_cov
      localparam logic [2:0] I = gi[2:0];
      localparam logic [7:0] CODE = 8'b0000_0001 << I;
      always_comb cover (in == I);
      always_comb cover (out == CODE);
      always_comb cover (in == I && out == CODE);
    end
  endgenerate

endmodule

bind decoder_3to8 decoder_3to8_sva sva_decoder_3to8 (.*);