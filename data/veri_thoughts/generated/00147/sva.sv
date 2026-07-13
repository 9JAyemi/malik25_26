module bin_to_decimal_sva (
    input logic        clk,
    input logic [15:0] B,
    input logic [19:0] bcdout
);

function automatic int unsigned bcd_value(input logic [19:0] bcd);
    begin
        bcd_value = (bcd[19:16] * 10000) +
                    (bcd[15:12] * 1000)  +
                    (bcd[11:8]  * 100)   +
                    (bcd[7:4]   * 10)    +
                     bcd[3:0];
    end
endfunction

// Ones nibble is a legal BCD digit.
check_ones_digit_valid: assert property (
    @(posedge clk) bcdout[3:0] <= 4'd9
);

// Tens nibble is a legal BCD digit.
check_tens_digit_valid: assert property (
    @(posedge clk) bcdout[7:4] <= 4'd9
);

// Hundreds nibble is a legal BCD digit.
check_hundreds_digit_valid: assert property (
    @(posedge clk) bcdout[11:8] <= 4'd9
);

// Thousands nibble is a legal BCD digit.
check_thousands_digit_valid: assert property (
    @(posedge clk) bcdout[15:12] <= 4'd9
);

// Ten-thousands nibble is a legal BCD digit.
check_ten_thousands_digit_valid: assert property (
    @(posedge clk) bcdout[19:16] <= 4'd9
);

// Packed BCD digits represent the same numeric value as B.
check_bcd_value_matches_input: assert property (
    @(posedge clk) bcd_value(bcdout) == B
);

// Single-digit inputs only use the ones nibble.
check_single_digit_mapping: assert property (
    @(posedge clk) (B <= 16'd9) |-> (bcdout == {16'd0, B[3:0]})
);

// Values below 100 keep the upper three BCD digits at zero.
check_two_digit_upper_digits_zero: assert property (
    @(posedge clk) (B < 16'd100) |-> (bcdout[19:8] == 12'd0)
);

// Values below 1000 keep the upper two BCD digits at zero.
check_three_digit_upper_digits_zero: assert property (
    @(posedge clk) (B < 16'd1000) |-> (bcdout[19:12] == 8'd0)
);

// Values below 10000 keep the ten-thousands digit at zero.
check_four_digit_top_digit_zero: assert property (
    @(posedge clk) (B < 16'd10000) |-> (bcdout[19:16] == 4'd0)
);

// Maximum input maps to 65535 in packed BCD.
check_max_input_mapping: assert property (
    @(posedge clk) (B == 16'd65535) |-> (bcdout == {4'd6, 4'd5, 4'd5, 4'd3, 4'd5})
);

endmodule