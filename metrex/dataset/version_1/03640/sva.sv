// SVA for decoder_4to16 (concise, high-quality, combinational checks + coverage)
module decoder_4to16_sva (input logic [3:0] in, input logic [15:0] out);
  // Core functional and integrity checks (only when inputs are 0/1 clean)
  always_comb begin
    if (!$isunknown(in)) begin
      assert (out == (16'h1 << in))
        else $error("decoder_4to16: out != 1<<in: in=%0h out=%0h", in, out);
      assert ($onehot(out))
        else $error("decoder_4to16: out not onehot: in=%0h out=%0h", in, out);
      assert (!$isunknown(out))
        else $error("decoder_4to16: X/Z on out for known in=%0h", in);
    end
  end

  // Coverage: every input code seen; every output bit asserted
  genvar i;
  generate
    for (i=0; i<16; i++) begin : COV
      cover property (@(posedge (in == i[3:0])) 1'b1);
      cover property (@(posedge out[i]) 1'b1);
    end
  endgenerate
endmodule

// Bind into DUT
bind decoder_4to16 decoder_4to16_sva u_decoder_4to16_sva (.in(in), .out(out));