module num_3_sva (
    input logic [2:0] in_row,
    input logic [4:0] out_code
);

    // RTL has no native clock/reset and implements combinational decode logic.
    // 000 and 101 must decode to 01110.
    check_d0_mapping: assert property (
        @($global_clock)
        ((in_row == 3'b000) || (in_row == 3'b101)) |-> (out_code == 5'b01110)
    );

    // 001 and 100 must decode to 10001.
    check_d1_mapping: assert property (
        @($global_clock)
        ((in_row == 3'b001) || (in_row == 3'b100)) |-> (out_code == 5'b10001)
    );

    // 010 must decode to 01000.
    check_d2_mapping: assert property (
        @($global_clock)
        (in_row == 3'b010) |-> (out_code == 5'b01000)
    );

    // 011 must decode to 10000.
    check_d3_mapping: assert property (
        @($global_clock)
        (in_row == 3'b011) |-> (out_code == 5'b10000)
    );

    // 110 and 111 must take the default zero code.
    check_default_mapping: assert property (
        @($global_clock)
        ((in_row == 3'b110) || (in_row == 3'b111)) |-> (out_code == 5'b00000)
    );

    // The output must always be one of the case-assigned codes.
    check_legal_output_values: assert property (
        @($global_clock)
        out_code inside {5'b01110, 5'b10001, 5'b01000, 5'b10000, 5'b00000}
    );

endmodule