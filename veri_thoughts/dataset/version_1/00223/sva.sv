module bitwise_or_sva(
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c
);

    // Output must equal the bitwise OR of the inputs.
    check_c_matches_or: assert property (
        @(posedge clk) (c == (a | b))
    );

    // Any high bit on a must remain high on c.
    check_a_ones_propagate: assert property (
        @(posedge clk) ((a & ~c) == 8'h00)
    );

    // Any high bit on b must remain high on c.
    check_b_ones_propagate: assert property (
        @(posedge clk) ((b & ~c) == 8'h00)
    );

    // c must not assert bits that are low on both inputs.
    check_c_has_no_extra_ones: assert property (
        @(posedge clk) ((c & ~(a | b)) == 8'h00)
    );

endmodule