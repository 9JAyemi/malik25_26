module BIN_DEC1_sva (
    input logic [15:0] B1,
    input logic [19:0] bcdout1
);

    function automatic int unsigned bcd_to_bin(input logic [19:0] bcd);
        int unsigned d4;
        int unsigned d3;
        int unsigned d2;
        int unsigned d1;
        int unsigned d0;
        begin
            d4 = bcd[19:16];
            d3 = bcd[15:12];
            d2 = bcd[11:8];
            d1 = bcd[7:4];
            d0 = bcd[3:0];
            bcd_to_bin = (d4 * 10000) + (d3 * 1000) + (d2 * 100) + (d1 * 10) + d0;
        end
    endfunction

    // Each output nibble must be a valid BCD digit.
    check_output_digits_are_valid_bcd: assert property (
        @($global_clock)
        (bcdout1[19:16] <= 4'd9) &&
        (bcdout1[15:12] <= 4'd9) &&
        (bcdout1[11:8]  <= 4'd9) &&
        (bcdout1[7:4]   <= 4'd9) &&
        (bcdout1[3:0]   <= 4'd9)
    );

    // The BCD output must reconstruct the original binary input.
    check_bcd_reconstructs_input: assert property (
        @($global_clock) bcd_to_bin(bcdout1) == B1
    );

    // Zero input must produce all-zero BCD digits.
    check_zero_maps_to_zero: assert property (
        @($global_clock) (B1 == 16'd0) |-> (bcdout1 == 20'd0)
    );

    // The maximum 16-bit input must encode as decimal 65535.
    check_max_maps_to_65535: assert property (
        @($global_clock) (B1 == 16'd65535) |-> (bcdout1 == 20'h65535)
    );

    // The ten-thousands digit cannot exceed 6 for a 16-bit input.
    check_ten_thousands_digit_range: assert property (
        @($global_clock) bcdout1[19:16] <= 4'd6
    );

    // Inputs below 10 must have zero in all upper BCD digits.
    check_single_digit_input_has_zero_upper_digits: assert property (
        @($global_clock) (B1 < 16'd10) |-> (bcdout1[19:4] == 16'd0)
    );

    // Inputs below 100 must have zero above the tens digit.
    check_two_digit_input_has_zero_upper_digits: assert property (
        @($global_clock) (B1 < 16'd100) |-> (bcdout1[19:8] == 12'd0)
    );

    // Inputs below 1000 must have zero above the hundreds digit.
    check_three_digit_input_has_zero_upper_digits: assert property (
        @($global_clock) (B1 < 16'd1000) |-> (bcdout1[19:12] == 8'd0)
    );

    // Inputs below 10000 must have a zero ten-thousands digit.
    check_four_digit_input_has_zero_top_digit: assert property (
        @($global_clock) (B1 < 16'd10000) |-> (bcdout1[19:16] == 4'd0)
    );

endmodule