// SVA for bin2gray: checks correct binary->Gray mapping and basic coverage.
// Bind these assertions to the DUT.

module bin2gray_sva(input logic [3:0] bin_in,
                    input logic [3:0] gray_out);

  // No X/Z on outputs when inputs are known
  assert property (@(*) !$isunknown(bin_in) |-> !$isunknown(gray_out));

  // Functional correctness: Gray = bin ^ (bin >> 1)
  assert property (@(*) !$isunknown(bin_in) |-> gray_out == (bin_in ^ (bin_in >> 1)));

  // Coverage: exercise all 16 input codes
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_cov_in
      localparam logic [3:0] VAL = i[3:0];
      cover property (@(*) bin_in == VAL);
    end
  endgenerate

  // Coverage: each output bit sees 0 and 1
  genvar b;
  generate
    for (b = 0; b < 4; b++) begin : g_cov_outbits
      cover property (@(*) gray_out[b] == 1'b0);
      cover property (@(*) gray_out[b] == 1'b1);
    end
  endgenerate

endmodule

bind bin2gray bin2gray_sva u_bin2gray_sva(.bin_in(bin_in), .gray_out(gray_out));