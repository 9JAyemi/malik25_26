// SVA for decoder_3to8
// Concise checks: functional equivalence, one-hotness, and full input-space coverage.
// Bind this file to the DUT.

`ifndef DECODER_3TO8_SVA
`define DECODER_3TO8_SVA
// synthesis translate_off

module decoder_3to8_sva (
  input  logic [2:0] in,
  input  logic [7:0] out
);

  // Functional equivalence when inputs are known
  always_comb begin
    if (!$isunknown(in)) begin
      assert (out === (8'b00000001 << in))
        else $error("decoder_3to8: out != (1<<in): in=%0d out=%b", in, out);
      assert ($onehot(out))
        else $error("decoder_3to8: out not onehot for in=%0d out=%b", in, out);
    end
  end

  // Full coverage: exercise every decode value and matching output
  genvar gi;
  generate
    for (gi = 0; gi < 8; gi++) begin : gen_cov
      localparam logic [2:0] IDX = gi[2:0];
      always_comb cover (!$isunknown(in) && (in == IDX) &&
                         (out == (8'b00000001 << IDX)));
    end
  endgenerate

endmodule

bind decoder_3to8 decoder_3to8_sva u_decoder_3to8_sva (.in(in), .out(out));

// synthesis translate_on
`endif