module BIN_DEC2_sva (
    input logic        clk,
    input logic [15:0] B2,
    input logic [19:0] bcdout2
);

    // Reconstructed decimal value must equal the binary input.
    check_decimal_value_match: assert property (
        @(posedge clk)
        ((int'(bcdout2[19:16]) * 10000) +
         (int'(bcdout2[15:12]) * 1000)  +
         (int'(bcdout2[11:8])  * 100)   +
         (int'(bcdout2[7:4])   * 10)    +
          int'(bcdout2[3:0])) == int'(B2)
    );

    // Ones nibble must be a valid BCD digit.
    check_ones_digit_range: assert property (
        @(posedge clk) bcdout2[3:0] <= 4'd9
    );

    // Tens nibble must be a valid BCD digit.
    check_tens_digit_range: assert property (
        @(posedge clk) bcdout2[7:4] <= 4'd9
    );

    // Hundreds nibble must be a valid BCD digit.
    check_hundreds_digit_range: assert property (
        @(posedge clk) bcdout2[11:8] <= 4'd9
    );

    // Thousands nibble must be a valid BCD digit.
    check_thousands_digit_range: assert property (
        @(posedge clk) bcdout2[15:12] <= 4'd9
    );

    // Ten-thousands nibble must be a valid BCD digit.
    check_ten_thousands_digit_range: assert property (
        @(posedge clk) bcdout2[19:16] <= 4'd9
    );

    // Zero converts to all-zero BCD.
    check_zero_conversion: assert property (
        @(posedge clk) (B2 == 16'd0) |-> (bcdout2 == 20'h00000)
    );

    // Ten converts to 00010 in BCD.
    check_ten_conversion: assert property (
        @(posedge clk) (B2 == 16'd10) |-> (bcdout2 == 20'h00010)
    );

    // Ten-thousand converts to 10000 in BCD.
    check_ten_thousand_conversion: assert property (
        @(posedge clk) (B2 == 16'd10000) |-> (bcdout2 == 20'h10000)
    );

    // Maximum 16-bit input converts to 65535 in BCD.
    check_max_conversion: assert property (
        @(posedge clk) (B2 == 16'd65535) |-> (bcdout2 == 20'h65535)
    );

    // Single-digit inputs only occupy the ones nibble.
    check_single_digit_conversion: assert property (
        @(posedge clk) (B2 <= 16'd9) |-> (bcdout2[19:4] == 16'h0000 && bcdout2[3:0] == B2[3:0])
    );

endmodule