module binary_to_gray_sva (
    input logic clk,
    input logic [2:0] bin_in,
    input logic [2:0] gray_out
);

    // gray_out matches the binary-to-gray conversion.
    check_gray_encoding: assert property (
        @(posedge clk) gray_out == {bin_in[2], (bin_in[1] ^ bin_in[2]), (bin_in[0] ^ bin_in[1])}
    );

    // The MSB of gray_out passes through bin_in[2].
    check_gray_msb_passthrough: assert property (
        @(posedge clk) gray_out[2] == bin_in[2]
    );

    // gray_out[1] is the XOR of bin_in[1] and bin_in[2].
    check_gray_mid_xor: assert property (
        @(posedge clk) gray_out[1] == (bin_in[1] ^ bin_in[2])
    );

    // gray_out[0] is the XOR of bin_in[0] and bin_in[1].
    check_gray_lsb_xor: assert property (
        @(posedge clk) gray_out[0] == (bin_in[0] ^ bin_in[1])
    );

    // A stable binary input yields a stable gray output.
    check_stable_input_stable_output: assert property (
        @(posedge clk) $stable(bin_in) |-> $stable(gray_out)
    );

endmodule