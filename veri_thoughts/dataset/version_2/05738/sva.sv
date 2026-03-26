module bin2gray_sva (
    input logic       rst,
    input logic [3:0] bin_in,
    input logic [3:0] gray_out
);

    // Combinational DUT is sampled on the formal global clock; rst is active high.

    // gray_out must match the binary-to-Gray conversion formula.
    check_gray_vector_encoding: assert property (
        @($global_clock) disable iff (rst)
        gray_out == {bin_in[3], (bin_in[3] ^ bin_in[2]), (bin_in[2] ^ bin_in[1]), (bin_in[1] ^ bin_in[0])}
    );

    // Gray MSB must pass through from the binary MSB.
    check_gray_msb_passthrough: assert property (
        @($global_clock) disable iff (rst)
        gray_out[3] == bin_in[3]
    );

    // gray_out[2] must be the XOR of bin_in[3] and bin_in[2].
    check_gray_bit2_xor: assert property (
        @($global_clock) disable iff (rst)
        gray_out[2] == (bin_in[3] ^ bin_in[2])
    );

    // gray_out[1] must be the XOR of bin_in[2] and bin_in[1].
    check_gray_bit1_xor: assert property (
        @($global_clock) disable iff (rst)
        gray_out[1] == (bin_in[2] ^ bin_in[1])
    );

    // gray_out[0] must be the XOR of bin_in[1] and bin_in[0].
    check_gray_lsb_xor: assert property (
        @($global_clock) disable iff (rst)
        gray_out[0] == (bin_in[1] ^ bin_in[0])
    );

endmodule