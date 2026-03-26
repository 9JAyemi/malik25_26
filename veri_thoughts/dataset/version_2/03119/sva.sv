module parity_calculator_sva (
    input logic        clk,
    input logic [15:0] data,
    input logic        parity
);

    // Parity equals the XOR reduction of all 16 data bits.
    check_parity_matches_reduction_xor: assert property (
        @(posedge clk) parity == (^data)
    );

    // Parity equals the XOR of the low-byte and high-byte parities.
    check_parity_matches_byte_parities: assert property (
        @(posedge clk) parity == ((^data[7:0]) ^ (^data[15:8]))
    );

    // Parity matches the pairwise XOR structure used in the RTL.
    check_parity_matches_pairwise_structure: assert property (
        @(posedge clk)
        parity == (
            (data[0]  ^ data[4])  ^
            (data[1]  ^ data[5])  ^
            (data[2]  ^ data[6])  ^
            (data[3]  ^ data[7])  ^
            (data[8]  ^ data[12]) ^
            (data[9]  ^ data[13]) ^
            (data[10] ^ data[14]) ^
            (data[11] ^ data[15])
        )
    );

    // All-zero input produces even parity.
    check_zero_data_even_parity: assert property (
        @(posedge clk) (data == 16'h0000) |-> (parity == 1'b0)
    );

    // All-one input produces even parity.
    check_all_ones_even_parity: assert property (
        @(posedge clk) (data == 16'hFFFF) |-> (parity == 1'b0)
    );

    // Any one-hot input produces odd parity.
    check_onehot_data_odd_parity: assert property (
        @(posedge clk) $onehot(data) |-> (parity == 1'b1)
    );

endmodule