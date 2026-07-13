module BCD_to_Binary_sva (
    input logic CLK,
    input logic [3:0] bcd_in,
    input logic [7:0] bin_out
);
    // For valid BCD (0..9), output equals zero-extended input.
    check_valid_mapping: assert property (
        @(posedge CLK) (bcd_in <= 4'd9) |-> (bin_out == {4'b0000, bcd_in})
    );

    // For invalid BCD (>9), output defaults to zero.
    check_invalid_defaults_to_zero: assert property (
        @(posedge CLK) (bcd_in >= 4'd10) |-> (bin_out == 8'd0)
    );

    // Upper nibble of output is always zero.
    check_upper_nibble_zero: assert property (
        @(posedge CLK) bin_out[7:4] == 4'b0000
    );

    // Output value is always between 0 and 9.
    check_output_range_0_to_9: assert property (
        @(posedge CLK) bin_out <= 8'd9
    );

    // If output is zero, input is either 0 or invalid (>9).
    check_zero_output_input_condition: assert property (
        @(posedge CLK) (bin_out == 8'd0) |-> ((bcd_in == 4'd0) || (bcd_in >= 4'd10))
    );

    // With stable input across cycles, output remains stable.
    check_stability_with_stable_input: assert property (
        @(posedge CLK) ($past(1'b1) && $stable(bcd_in)) |-> $stable(bin_out)
    );

    // Between two valid inputs, a change in input implies a change in output.
    check_injective_on_valid_inputs: assert property (
        @(posedge CLK) ($past(1'b1) && ($past(bcd_in) <= 4'd9) && (bcd_in <= 4'd9) && ($past(bcd_in) != bcd_in)) |-> ($past(bin_out) != bin_out)
    );

    // Output remains zero across consecutive invalid inputs.
    check_zero_held_on_consecutive_invalid: assert property (
        @(posedge CLK) ($past(1'b1) && ($past(bcd_in) >= 4'd10) && (bcd_in >= 4'd10)) |-> (($past(bin_out) == 8'd0) && (bin_out == 8'd0))
    );

    // For valid inputs, lower nibble equals input value.
    check_lower_nibble_matches_on_valid: assert property (
        @(posedge CLK) (bcd_in <= 4'd9) |-> (bin_out[3:0] == bcd_in)
    );

    // For invalid inputs, lower nibble is zero.
    check_lower_nibble_zero_on_invalid: assert property (
        @(posedge CLK) (bcd_in >= 4'd10) |-> (bin_out[3:0] == 4'd0)
    );
endmodule