module sum_2_msb_sva (
    input logic       clk,
    input logic [3:0] in_4,
    input logic [1:0] out_2
);

    // Output bit 1 is the OR of the two input MSBs.
    check_out2_bit1_is_msb_or: assert property (
        @(posedge clk) out_2[1] == (in_4[3] | in_4[2])
    );

    // Output bit 0 is the OR of the two input MSBs.
    check_out2_bit0_is_msb_or: assert property (
        @(posedge clk) out_2[0] == (in_4[3] | in_4[2])
    );

    // Both output bits always match because the OR result is replicated.
    check_out2_bits_match: assert property (
        @(posedge clk) out_2[1] == out_2[0]
    );

    // When both input MSBs are low, the output is 2'b00.
    check_zero_when_both_msbs_low: assert property (
        @(posedge clk) (in_4[3:2] == 2'b00) |-> (out_2 == 2'b00)
    );

    // When either input MSB is high, the output is 2'b11.
    check_ones_when_any_msb_high: assert property (
        @(posedge clk) (in_4[3] | in_4[2]) |-> (out_2 == 2'b11)
    );

endmodule