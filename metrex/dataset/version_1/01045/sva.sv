// SVA checker for decoder. Bind this to the DUT.
module decoder_sva (
  input logic [3:0]  ABCD,
  input logic [15:0] out
);

  // Expected decode
  function automatic logic [15:0] exp_out (input logic [3:0] a);
    exp_out = 16'h1 << a;
  endfunction

  // Combinational correctness and X-handling (immediate assertions for robust @* sampling)
  always_comb begin
    if (!$isunknown(ABCD)) begin
      assert (out == exp_out(ABCD)) else $error("Decode mismatch: ABCD=%0d out=%h exp=%h", ABCD, out, exp_out(ABCD));
      assert ($onehot(out))          else $error("Output not one-hot for ABCD=%0d out=%h", ABCD, out);
      assert (!$isunknown(out))      else $error("Output has X/Z for ABCD=%0d out=%h", ABCD, out);
      assert (out != 16'h0)          else $error("Output zero with known input ABCD=%0d", ABCD);
    end
    else begin
      // With unknown input, RTL default should drive zero
      assert (out == 16'h0)          else $error("Unknown ABCD must drive out=0, got %h", out);
    end
  end

  // Coverage: hit all 16 input codes and correct decode each time
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cov_val
      cover property (@(ABCD) (ABCD == i) && (out == (16'h1 << i)));
    end
  endgenerate

endmodule

// Bind to DUT
bind decoder decoder_sva u_decoder_sva (.ABCD(ABCD), .out(out));