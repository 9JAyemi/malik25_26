module gray_code_sva (
    input logic clk,
    input logic [7:0] data_in,
    input logic [7:0] gray_out
);

    // gray_out[0] equals data_in[0].
    check_gray_bit0_is_d0: assert property (
        @(posedge clk) gray_out[0] == data_in[0]
    );

    // gray_out[1] equals data_in[0] XOR data_in[1].
    check_gray_bit1_is_d0_xor_d1: assert property (
        @(posedge clk) gray_out[1] == (data_in[0] ^ data_in[1])
    );

    // gray_out[2] equals data_in[1] XOR data_in[2].
    check_gray_bit2_is_d1_xor_d2: assert property (
        @(posedge clk) gray_out[2] == (data_in[1] ^ data_in[2])
    );

    // gray_out[3] equals data_in[2] XOR data_in[3].
    check_gray_bit3_is_d2_xor_d3: assert property (
        @(posedge clk) gray_out[3] == (data_in[2] ^ data_in[3])
    );

    // gray_out[4] equals data_in[3] XOR data_in[4].
    check_gray_bit4_is_d3_xor_d4: assert property (
        @(posedge clk) gray_out[4] == (data_in[3] ^ data_in[4])
    );

    // gray_out[5] equals data_in[4] XOR data_in[5].
    check_gray_bit5_is_d4_xor_d5: assert property (
        @(posedge clk) gray_out[5] == (data_in[4] ^ data_in[5])
    );

    // gray_out[6] equals data_in[5] XOR data_in[6].
    check_gray_bit6_is_d5_xor_d6: assert property (
        @(posedge clk) gray_out[6] == (data_in[5] ^ data_in[6])
    );

    // gray_out[7] equals data_in[6] XOR data_in[7].
    check_gray_bit7_is_d6_xor_d7: assert property (
        @(posedge clk) gray_out[7] == (data_in[6] ^ data_in[7])
    );

endmodule