module GrayCodeConverter_sva #(
  parameter int n = 4
)(
  // External clock for checking combinational logic
  input logic CLK,

  // DUT ports
  input logic [n-1:0] bin,
  input logic [n-1:0] gray,
  input logic [n-1:0] gray_out,
  input logic [n-1:0] bin_out
);
  // No reset in RTL; pure combinational; assertions are clocked on CLK.

  // gray_out must equal bin XOR (bin >> 1).
  check_gray_out_def: assert property (
    @(posedge CLK) gray_out == (bin ^ (bin >> 1))
  );

  // bin_out must equal gray XOR (gray >> 1).
  check_bin_out_def: assert property (
    @(posedge CLK) bin_out == (gray ^ (gray >> 1))
  );

  // MSB of gray_out equals MSB of bin.
  check_gray_msb: assert property (
    @(posedge CLK) gray_out[n-1] == bin[n-1]
  );

  // MSB of bin_out equals MSB of gray.
  check_bin_msb: assert property (
    @(posedge CLK) bin_out[n-1] == gray[n-1]
  );

  // Each gray_out[i] equals bin[i] XOR bin[i+1] for i in [0..n-2].
  genvar gi;
  generate
    for (gi = 0; gi < (n-1); gi++) begin : gen_gray_bits
      check_gray_bit: assert property (
        @(posedge CLK) gray_out[gi] == (bin[gi] ^ bin[gi+1])
      );
    end
  endgenerate

  // Each bin_out[i] equals gray[i] XOR gray[i+1] for i in [0..n-2].
  genvar bi;
  generate
    for (bi = 0; bi < (n-1); bi++) begin : gen_bin_bits
      check_bin_bit: assert property (
        @(posedge CLK) bin_out[bi] == (gray[bi] ^ gray[bi+1])
      );
    end
  endgenerate

  // When bin is all-zeros, gray_out must be all-zeros.
  check_zero_bin_to_zero_gray: assert property (
    @(posedge CLK) (bin == '0) |-> (gray_out == '0)
  );

  // When gray is all-zeros, bin_out must be all-zeros.
  check_zero_gray_to_zero_bin: assert property (
    @(posedge CLK) (gray == '0) |-> (bin_out == '0)
  );

  // gray_out XOR bin equals bin right-shifted by 1.
  check_gray_xor_bin_is_shift: assert property (
    @(posedge CLK) (gray_out ^ bin) == (bin >> 1)
  );

  // bin_out XOR gray equals gray right-shifted by 1.
  check_bin_xor_gray_is_shift: assert property (
    @(posedge CLK) (bin_out ^ gray) == (gray >> 1)
  );

endmodule