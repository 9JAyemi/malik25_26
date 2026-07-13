module binary_to_bcd_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [7:0] Z
);

    // Inputs 0 through 9 map directly to the low BCD digit.
    check_single_digit_conversion: assert property (
        @(posedge clk) (A <= 4'd9) |-> (Z == {4'h0, A})
    );

    // Inputs 10 through 15 map to BCD with tens digit 1.
    check_ten_to_fifteen_conversion: assert property (
        @(posedge clk) (A >= 4'd10) |-> (Z == {4'h1, (A - 4'd10)})
    );

    // Inputs below ten keep the tens digit at zero.
    check_tens_digit_below_ten: assert property (
        @(posedge clk) (A <= 4'd9) |-> (Z[7:4] == 4'h0)
    );

    // Inputs ten and above drive the tens digit to one.
    check_tens_digit_ten_or_more: assert property (
        @(posedge clk) (A >= 4'd10) |-> (Z[7:4] == 4'h1)
    );

    // Inputs below ten keep the ones digit equal to the input.
    check_ones_digit_below_ten: assert property (
        @(posedge clk) (A <= 4'd9) |-> (Z[3:0] == A)
    );

    // Inputs ten and above drive the ones digit to input minus ten.
    check_ones_digit_ten_or_more: assert property (
        @(posedge clk) (A >= 4'd10) |-> (Z[3:0] == (A - 4'd10))
    );

endmodule