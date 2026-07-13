module bin_to_bcd_sva (
    input logic        clk,
    input logic [3:0]  bin,
    input logic [3:0]  bcd1,
    input logic [3:0]  bcd2,
    input logic [3:0]  bcd3,
    input logic [3:0]  bcd4
);

    // bcd1 must match the decimal ones digit of bin.
    check_ones_digit_matches_bin: assert property (
        @(posedge clk) bcd1 == (bin % 4'd10)
    );

    // bcd2 must match the decimal tens digit of bin.
    check_tens_digit_matches_bin: assert property (
        @(posedge clk) bcd2 == (bin / 4'd10)
    );

    // bcd3 is always zero for a 4-bit binary input range.
    check_hundreds_digit_zero: assert property (
        @(posedge clk) bcd3 == 4'd0
    );

    // bcd4 is always zero for a 4-bit binary input range.
    check_thousands_digit_zero: assert property (
        @(posedge clk) bcd4 == 4'd0
    );

    // All output digits must remain valid BCD values.
    check_output_digits_are_valid_bcd: assert property (
        @(posedge clk) (bcd1 <= 4'd9) && (bcd2 <= 4'd9) && (bcd3 <= 4'd9) && (bcd4 <= 4'd9)
    );

    // Inputs below 10 must produce only a ones digit.
    check_single_digit_input_mapping: assert property (
        @(posedge clk) (bin < 4'd10) |-> (bcd1 == bin) && (bcd2 == 4'd0) && (bcd3 == 4'd0) && (bcd4 == 4'd0)
    );

    // Inputs 10 through 15 must produce tens digit 1 and the proper ones digit.
    check_10_to_15_input_mapping: assert property (
        @(posedge clk) (bin >= 4'd10) |-> (bcd1 == (bin - 4'd10)) && (bcd2 == 4'd1) && (bcd3 == 4'd0) && (bcd4 == 4'd0)
    );

    // Zero input must convert to all zero BCD digits.
    check_zero_input_maps_to_zero: assert property (
        @(posedge clk) (bin == 4'd0) |-> (bcd1 == 4'd0) && (bcd2 == 4'd0) && (bcd3 == 4'd0) && (bcd4 == 4'd0)
    );

endmodule