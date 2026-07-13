module my_nand2b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B
);

// Y equals (~B) & (~A_N).
    check_function_equivalence: assert property (
        @(posedge clk) Y == ((~B) & (~A_N))
    );

// When both inputs are LOW, Y must be HIGH.
    check_both_low_drives_high: assert property (
        @(posedge clk) (!B && !A_N) |-> (Y == 1'b1)
    );

// If B is HIGH, Y must be LOW.
    check_b_high_drives_low: assert property (
        @(posedge clk) (B == 1'b1) |-> (Y == 1'b0)
    );

// If A_N is HIGH, Y must be LOW.
    check_an_high_drives_low: assert property (
        @(posedge clk) (A_N == 1'b1) |-> (Y == 1'b0)
    );

// If Y is HIGH, both inputs must be LOW.
    check_high_output_requires_both_low: assert property (
        @(posedge clk) (Y == 1'b1) |-> (!B && !A_N)
    );

// If Y is LOW, at least one input must be HIGH.
    check_low_output_requires_some_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> (B || A_N)
    );

endmodule
