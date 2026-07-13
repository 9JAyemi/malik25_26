module divide_by12_sva (
    input logic [5:0] numer,
    input logic [2:0] quotient,
    input logic [3:0] remain
);

    // No RTL clock or reset; sample on the formal global clock.

    // Quotient matches division by 12.
    check_quotient_div12: assert property (
        @($global_clock) quotient == (numer / 6'd12)
    );

    // Remainder matches modulo 12.
    check_remain_mod12: assert property (
        @($global_clock) remain == (numer % 6'd12)
    );

    // Low remainder bits copy directly from the input.
    check_remain_low_bits_copy: assert property (
        @($global_clock) remain[1:0] == numer[1:0]
    );

    // High remainder bits equal the upper input bits modulo 3.
    check_remain_high_bits_mod3: assert property (
        @($global_clock) remain[3:2] == (numer[5:2] % 4'd3)
    );

    // Quotient equals the upper input bits divided by 3.
    check_quotient_upper_div3: assert property (
        @($global_clock) quotient == (numer[5:2] / 4'd3)
    );

    // Quotient stays within the implemented output range.
    check_quotient_range: assert property (
        @($global_clock) quotient <= 3'd5
    );

    // Upper remainder bits never exceed decimal 2.
    check_remain_high_range: assert property (
        @($global_clock) remain[3:2] <= 2'd2
    );

    // Quotient and remainder reconstruct the input.
    check_division_identity: assert property (
        @($global_clock) {1'b0, numer} == ((quotient * 4'd12) + remain)
    );

    // The lowest input value maps to zero quotient and remainder.
    check_zero_input_case: assert property (
        @($global_clock) (numer == 6'd0) |-> ((quotient == 3'd0) && (remain == 4'd0))
    );

    // The highest input value maps to quotient 5 and remainder 3.
    check_max_input_case: assert property (
        @($global_clock) (numer == 6'd63) |-> ((quotient == 3'd5) && (remain == 4'd3))
    );

endmodule