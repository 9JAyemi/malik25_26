module gray_to_bin8_sva (
    input logic clk,
    input logic [7:0] gray_input,
    input logic [7:0] bin_out
);
    // MSB of binary equals MSB of Gray.
    check_msb_mapping: assert property (
        @(posedge clk) bin_out[7] == gray_input[7]
    );

    // bin_out[6] equals bin_out[7] XOR gray_input[6].
    check_chain_b6: assert property (
        @(posedge clk) bin_out[6] == (bin_out[7] ^ gray_input[6])
    );

    // bin_out[5] equals bin_out[6] XOR gray_input[5].
    check_chain_b5: assert property (
        @(posedge clk) bin_out[5] == (bin_out[6] ^ gray_input[5])
    );

    // bin_out[4] equals bin_out[5] XOR gray_input[4].
    check_chain_b4: assert property (
        @(posedge clk) bin_out[4] == (bin_out[5] ^ gray_input[4])
    );

    // bin_out[3] equals bin_out[4] XOR gray_input[3].
    check_chain_b3: assert property (
        @(posedge clk) bin_out[3] == (bin_out[4] ^ gray_input[3])
    );

    // bin_out[2] equals bin_out[3] XOR gray_input[2].
    check_chain_b2: assert property (
        @(posedge clk) bin_out[2] == (bin_out[3] ^ gray_input[2])
    );

    // bin_out[1] equals bin_out[2] XOR gray_input[1].
    check_chain_b1: assert property (
        @(posedge clk) bin_out[1] == (bin_out[2] ^ gray_input[1])
    );

    // bin_out[0] equals bin_out[1] XOR gray_input[0].
    check_chain_b0: assert property (
        @(posedge clk) bin_out[0] == (bin_out[1] ^ gray_input[0])
    );
endmodule