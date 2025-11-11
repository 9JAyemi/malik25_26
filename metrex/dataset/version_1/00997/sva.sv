// SVA checker for decoder_4to16
module decoder_4to16_sva (
  input logic [3:0]  in,
  input logic [15:0] out,
  // optional bind to internal net for sanity check
  input logic [15:0] temp
);

  // Functional equivalence and one-hot correctness when inputs are known
  always_comb begin
    if (!$isunknown(in)) begin
      assert (out == (16'h0001 << in))
        else $error("decoder mapping mismatch: in=%0d out=%h", in, out);
      assert ($onehot(out))
        else $error("decoder out not onehot: in=%0d out=%h", in, out);
      assert (!$isunknown(out))
        else $error("decoder out has X/Z with known input: in=%0d out=%h", in, out);
    end
  end

  // Bit-wise mapping checks and functional coverage of all codes
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : G_BIT
      always_comb begin
        if (!$isunknown(in)) begin
          assert (out[i] == (in == i[3:0]))
            else $error("decoder bit mismatch: in=%0d out[%0d]=%0b", in, i, out[i]);
          cover (in == i[3:0] && out[i]); // hit each code
        end
      end
    end
  endgenerate

  // Sanity: internal net should equal out if connected via bind
  always_comb begin
    if (!$isunknown(temp)) begin
      assert (out === temp)
        else $error("decoder out != temp: out=%h temp=%h", out, temp);
    end
  end

endmodule

// Bind this checker to the DUT instance(s)
bind decoder_4to16 decoder_4to16_sva u_decoder_4to16_sva (
  .in  (in),
  .out (out),
  .temp(temp) // optional; remove or tie off if not available
);