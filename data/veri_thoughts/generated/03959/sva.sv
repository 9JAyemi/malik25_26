module xor_gate_sva (
    input logic         clk,
    input logic [99:0]  data_in_1,
    input logic [7:0]   data_in_2,
    input logic [99:0]  data_out
);

    // Full output must match the implemented XOR with zero-extended data_in_2.
    check_full_xor_relation: assert property (
        @(posedge clk) data_out == (data_in_1 ^ {92'b0, data_in_2})
    );

    // Upper 92 bits of the output must pass through from data_in_1 unchanged.
    check_upper_bits_passthrough: assert property (
        @(posedge clk) data_out[99:8] == data_in_1[99:8]
    );

    // Lower 8 bits of the output must be the XOR of the lower byte and data_in_2.
    check_lower_byte_xor_relation: assert property (
        @(posedge clk) data_out[7:0] == (data_in_1[7:0] ^ data_in_2)
    );

    // XORing the output lower byte with data_in_1 lower byte must recover data_in_2.
    check_lower_byte_recovers_input2: assert property (
        @(posedge clk) (data_out[7:0] ^ data_in_1[7:0]) == data_in_2
    );

    // A zero data_in_2 must make the output identical to data_in_1.
    check_zero_data_in_2_passthrough: assert property (
        @(posedge clk) (data_in_2 == 8'h00) |-> (data_out == data_in_1)
    );

    // A zero data_in_1 must make the output the zero-extended data_in_2.
    check_zero_data_in_1_zero_extended_output: assert property (
        @(posedge clk) (data_in_1 == 100'b0) |-> (data_out == {92'b0, data_in_2})
    );

    // Matching lower-byte inputs must cancel to zero on the lower output byte.
    check_matching_lower_bytes_cancel: assert property (
        @(posedge clk) (data_in_2 == data_in_1[7:0]) |-> (data_out[7:0] == 8'h00)
    );

endmodule