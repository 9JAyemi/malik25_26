module BCD_Converter_sva (
    input logic clk,
    input logic [3:0] bin,
    input logic [3:0] bcd
);

    // bcd[3] is high only for an all-ones input.
    check_bcd_bit3_all_ones: assert property (
        @(posedge clk)
        (bcd[3] == (bin == 4'b1111))
    );

    // bcd[2] is high for the four three-ones input patterns.
    check_bcd_bit2_three_high_patterns: assert property (
        @(posedge clk)
        (bcd[2] == (
            (bin == 4'b0111) ||
            (bin == 4'b1011) ||
            (bin == 4'b1101) ||
            (bin == 4'b1110)
        ))
    );

    // bcd[1] is high for the four patterns encoded by the RTL.
    check_bcd_bit1_selected_patterns: assert property (
        @(posedge clk)
        (bcd[1] == (
            (bin == 4'b0011) ||
            (bin == 4'b0110) ||
            (bin == 4'b1001) ||
            (bin == 4'b1100)
        ))
    );

    // bcd[0] is high for the four patterns encoded by the RTL.
    check_bcd_bit0_selected_patterns: assert property (
        @(posedge clk)
        (bcd[0] == (
            (bin == 4'b0001) ||
            (bin == 4'b1000) ||
            (bin == 4'b1010) ||
            (bin == 4'b1100)
        ))
    );

    // Inputs 0, 2, 4, and 5 produce a zero output.
    check_zero_output_cases: assert property (
        @(posedge clk)
        (
            (bin == 4'b0000) ||
            (bin == 4'b0010) ||
            (bin == 4'b0100) ||
            (bin == 4'b0101)
        ) |-> (bcd == 4'b0000)
    );

    // Inputs 1, 8, and 10 produce 0001.
    check_one_output_cases: assert property (
        @(posedge clk)
        (
            (bin == 4'b0001) ||
            (bin == 4'b1000) ||
            (bin == 4'b1010)
        ) |-> (bcd == 4'b0001)
    );

    // Inputs 3, 6, and 9 produce 0010.
    check_two_output_cases: assert property (
        @(posedge clk)
        (
            (bin == 4'b0011) ||
            (bin == 4'b0110) ||
            (bin == 4'b1001)
        ) |-> (bcd == 4'b0010)
    );

    // Inputs 7, 11, 13, and 14 produce 0100.
    check_four_output_cases: assert property (
        @(posedge clk)
        (
            (bin == 4'b0111) ||
            (bin == 4'b1011) ||
            (bin == 4'b1101) ||
            (bin == 4'b1110)
        ) |-> (bcd == 4'b0100)
    );

    // Input 12 is the only case that produces 0011.
    check_three_output_case: assert property (
        @(posedge clk)
        (bin == 4'b1100) |-> (bcd == 4'b0011)
    );

    // Input 15 produces 1000.
    check_eight_output_case: assert property (
        @(posedge clk)
        (bin == 4'b1111) |-> (bcd == 4'b1000)
    );

endmodule