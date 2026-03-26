module sky130_fd_sc_hdll__or2_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B
);

    // X must always equal the OR of A and B.
    check_or_equivalence: assert property (
        @(posedge clk) X == (A | B)
    );

    // If both inputs are low, the output must be low.
    check_or_both_low: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0)) |-> (X == 1'b0)
    );

    // If only A is high, the output must be high.
    check_or_a_only_high: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b0)) |-> (X == 1'b1)
    );

    // If only B is high, the output must be high.
    check_or_b_only_high: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b1)) |-> (X == 1'b1)
    );

    // If both inputs are high, the output must be high.
    check_or_both_high: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b1)) |-> (X == 1'b1)
    );

endmodule