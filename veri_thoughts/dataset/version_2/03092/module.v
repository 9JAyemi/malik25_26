module min_finder (
    input [7:0] a, b, c, d,
    output [7:0] min);

    wire [7:0] ab_min, cd_min;
    wire [7:0] abcd_min;

    // Stage 1
    // Compare a and b
    assign ab_min = (a < b) ? a : b;

    // Compare c and d
    assign cd_min = (c < d) ? c : d;

    // Stage 2
    // Compare ab_min and cd_min
    assign abcd_min = (ab_min < cd_min) ? ab_min : cd_min;

    // Output the minimum value
    assign min = abcd_min;

endmodule