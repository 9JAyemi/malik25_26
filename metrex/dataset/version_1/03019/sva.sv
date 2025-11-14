// SVA for GrayCodeConverter
`ifndef GRAY_CODE_CONVERTER_SVA_SV
`define GRAY_CODE_CONVERTER_SVA_SV

module GrayCodeConverter_sva #(parameter int n = 4)
(
  input logic [n-1:0] bin,
  input logic [n-1:0] gray,
  input logic [n-1:0] gray_out,
  input logic [n-1:0] bin_out
);

  // Reference encode/decode
  function automatic logic [n-1:0] enc_gray(input logic [n-1:0] b);
    enc_gray = b ^ (b >> 1);
  endfunction

  function automatic logic [n-1:0] dec_gray(input logic [n-1:0] g);
    logic [n-1:0] r;
    for (int i = n-1; i >= 0; i--) r[i] = ^g[n-1:i];
    dec_gray = r;
  endfunction

  // Combinational correctness and X-propagation checks
  always_comb begin
    if (!$isunknown(bin))  assert (!$isunknown(gray_out))
      else $error("gray_out has X/Z while bin is known");
    if (!$isunknown(gray)) assert (!$isunknown(bin_out))
      else $error("bin_out has X/Z while gray is known");

    assert (gray_out === enc_gray(bin))
      else $error("gray_out mismatch. exp=%0h got=%0h bin=%0h",
                  enc_gray(bin), gray_out, bin);

    assert (bin_out === dec_gray(gray))
      else $error("bin_out mismatch. exp=%0h got=%0h gray=%0h",
                  dec_gray(gray), bin_out, gray);

    // Round-trip cross-checks
    assert (dec_gray(gray_out) === bin)
      else $error("dec_gray(gray_out)!=bin. got=%0h bin=%0h",
                  dec_gray(gray_out), bin);
    assert (enc_gray(bin_out) === gray)
      else $error("enc_gray(bin_out)!=gray. got=%0h gray=%0h",
                  enc_gray(bin_out), gray);

    // Bitwise decode check: b[i] = ^g[n-1:i]
    for (int i = 0; i < n; i++) begin
      assert (bin_out[i] === (^gray[n-1:i]))
        else $error("bin_out[%0d] != ^gray[%0d:%0d]", i, n-1, i);
    end
  end

  // Minimal toggle coverage for all I/Os
  genvar gi;
  generate
    for (gi = 0; gi < n; gi++) begin : cov_bits
      cover property (@(posedge bin[gi])) 1;
      cover property (@(negedge bin[gi])) 1;
      cover property (@(posedge gray[gi])) 1;
      cover property (@(negedge gray[gi])) 1;
      cover property (@(posedge gray_out[gi])) 1;
      cover property (@(negedge gray_out[gi])) 1;
      cover property (@(posedge bin_out[gi])) 1;
      cover property (@(negedge bin_out[gi])) 1;
    end
  endgenerate

endmodule

// Bind into DUT
bind GrayCodeConverter GrayCodeConverter_sva #(.n(n)) u_graycode_sva (.*);

`endif