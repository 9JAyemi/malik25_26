module digit_sva (
    input logic clk,
    input logic [2:0] line,
    input logic [3:0] pixels
);

    // line==000 maps to 1110
    map_line_000_to_1110: assert property (
        @(posedge clk) (line == 3'b000) |-> (pixels == 4'b1110)
    );

    // line==001 maps to 1010
    map_line_001_to_1010: assert property (
        @(posedge clk) (line == 3'b001) |-> (pixels == 4'b1010)
    );

    // line==010 maps to 1010
    map_line_010_to_1010: assert property (
        @(posedge clk) (line == 3'b010) |-> (pixels == 4'b1010)
    );

    // line==011 maps to 1010
    map_line_011_to_1010: assert property (
        @(posedge clk) (line == 3'b011) |-> (pixels == 4'b1010)
    );

    // line==100 maps to 1110
    map_line_100_to_1110: assert property (
        @(posedge clk) (line == 3'b100) |-> (pixels == 4'b1110)
    );

    // line in 101/110/111 maps to 0000 (default)
    map_default_high_lines_to_0000: assert property (
        @(posedge clk) (line inside {3'b101,3'b110,3'b111}) |-> (pixels == 4'b0000)
    );

    // Pixels are only one of the three encoded patterns
    pixels_only_expected_values: assert property (
        @(posedge clk) (pixels inside {4'b1110,4'b1010,4'b0000})
    );

    // LSB of pixels is always 0
    pixel0_always_zero: assert property (
        @(posedge clk) (pixels[0] == 1'b0)
    );

    // pixels[3] equals pixels[2] for all cases
    pixels3_equals_pixels2: assert property (
        @(posedge clk) (pixels[3] == pixels[2])
    );

    // Non-default lines produce non-zero pixels
    nonzero_when_specified_line: assert property (
        @(posedge clk) (line inside {3'b000,3'b001,3'b010,3'b011,3'b100}) |-> (pixels != 4'b0000)
    );

    // Zero pixels imply default lines (101/110/111)
    zero_pixels_implies_default_lines: assert property (
        @(posedge clk) (pixels == 4'b0000) |-> (line inside {3'b101,3'b110,3'b111})
    );

    // 1110 pixels only for lines 000 or 100
    code_1110_implies_end_lines: assert property (
        @(posedge clk) (pixels == 4'b1110) |-> (line == 3'b000 || line == 3'b100)
    );

    // 1010 pixels only for lines 001..011
    code_1010_implies_mid_lines: assert property (
        @(posedge clk) (pixels == 4'b1010) |-> (line inside {[3'b001:3'b011]})
    );

endmodule