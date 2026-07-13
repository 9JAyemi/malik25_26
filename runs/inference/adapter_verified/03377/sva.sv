module hex_display_sva (
    input logic clk,
    input logic [3:0] in,
    input logic enable,
    input logic [6:0] out,
    input logic INVERT
);

// When enable is low, the output must be 0000000.
    check_disable_clears_output: assert property (
        @(posedge clk) !enable |-> (out == 7'b0000000)
    );

// When enable is high, out must match the selected 7-seg code.
    check_enable_selects_code: assert property (
        @(posedge clk) enable |-> (out == expected_code(in))
    );

// When enable is high, out must be one of the 7-seg encodings.
    check_enable_has_valid_code: assert property (
        @(posedge clk) enable |-> (valid_code(out))
    );

// When enable is high, out must not be 0000000.
    check_enable_has_nonzero_code: assert property (
        @(posedge clk) enable |-> (out != 7'b0000000)
    );

// When enable is high, out must not be 1111111.
    check_enable_not_all_ones: assert property (
        @(posedge clk) enable |-> (out != 7'b1111111)
    );

// When enable is high, out must not be 1111110.
    check_enable_not_all_ones_minus_one: assert property (
        @(posedge clk) enable |-> (out != 7'b1111110)
    );

// When enable is high, out must not be 1111100.
    check_enable_not_all_ones_minus_two: assert property (
        @(posedge clk) enable |-> (out != 7'b1111100)
    );

// When enable is high, out must not be 1111000.
    check_enable_not_all_ones_minus_four: assert property (
        @(posedge clk) enable |-> (out != 7'b1111000)
    );

// When enable is high, out must not be 1110000.
    check_enable_not_all_ones_minus_eight: assert property (
        @(posedge clk) enable |-> (out != 7'b1110000)
    );

// When enable is high, out must not be 1100000.
    check_enable_not_all_ones_minus_sixteen: assert property (
        @(posedge clk) enable |-> (out != 7'b1100000)
    );

// When enable is high, out must not be 1000000.
    check_enable_not_all_ones_minus_twenty_four: assert property (
        @(posedge clk) enable |-> (out != 7'b1000000)
    );

endmodule
