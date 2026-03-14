module min_finder (
    input [7:0] a, b, c, d,
    output [7:0] min);

    wire [7:0] ab_min, cd_min, global_min;

    // Comparators to find the minimum of a and b, and c and d
    assign ab_min = (a < b) ? a : b;
    assign cd_min = (c < d) ? c : d;

    // Multiplexer to select the minimum of a and b, and c and d
    assign global_min = (ab_min < cd_min) ? ab_min : cd_min;

    // Output the global minimum
    assign min = global_min;

endmodule

module top_module (
    input [7:0] a, b, c, d,
    output [7:0] min);

    min_finder min_finder_inst (
        .a(a),
        .b(b),
        .c(c),
        .d(d),
        .min(min)
    );

endmodule