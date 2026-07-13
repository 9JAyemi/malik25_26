module bcd_converter_assertions (
    input logic [3:0]  input_val,
    input logic [15:0] bcd_val
);

    function automatic logic [15:0] expected_bcd(input logic [3:0] val);
        case (val)
            4'b0000: expected_bcd = 16'b0000000000000000;
            4'b0001: expected_bcd = 16'b0000000000000001;
            4'b0010: expected_bcd = 16'b0000000000000010;
            4'b0011: expected_bcd = 16'b0000000000000011;
            4'b0100: expected_bcd = 16'b0000000000000100;
            4'b0101: expected_bcd = 16'b0000000000000101;
            4'b0110: expected_bcd = 16'b0000000000000110;
            4'b0111: expected_bcd = 16'b0000000000000111;
            4'b1000: expected_bcd = 16'b0000000000010000;
            4'b1001: expected_bcd = 16'b0000000000010001;
            default: expected_bcd = 16'b0000000000000000;
        endcase
    endfunction

    // Output matches the implemented case mapping for every input value.
    check_exact_case_mapping: assert property (
        @($global_clock) bcd_val == expected_bcd(input_val)
    );

    // Inputs 0 through 7 map directly into the low nibble with upper bits clear.
    check_zero_to_seven_direct_mapping: assert property (
        @($global_clock) (input_val <= 4'd7) |-> ((bcd_val[15:4] == 12'h000) && (bcd_val[3:0] == input_val))
    );

    // Input 8 maps to 16'h0010.
    check_input_eight_mapping: assert property (
        @($global_clock) (input_val == 4'd8) |-> (bcd_val == 16'h0010)
    );

    // Input 9 maps to 16'h0011.
    check_input_nine_mapping: assert property (
        @($global_clock) (input_val == 4'd9) |-> (bcd_val == 16'h0011)
    );

    // Inputs 10 through 15 select the default zero output.
    check_default_zero_for_ten_to_fifteen: assert property (
        @($global_clock) (input_val >= 4'd10) |-> (bcd_val == 16'h0000)
    );

    // The upper byte is always zero for all implemented outputs.
    check_upper_byte_zero: assert property (
        @($global_clock) (bcd_val[15:8] == 8'h00)
    );

endmodule