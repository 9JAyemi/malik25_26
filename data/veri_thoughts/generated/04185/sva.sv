module and4_sva (
    input logic clk,
    input logic X,
    input logic A_N,
    input logic B,
    input logic C,
    input logic D
);

    // X matches the inverted four-input AND function.
    check_x_function: assert property (
        @(posedge clk) (X == ~(A_N & B & C & D))
    );

    // When all inputs are high, X must be low.
    check_all_high_drives_x_low: assert property (
        @(posedge clk) (A_N & B & C & D) |-> (X == 1'b0)
    );

    // If X is low, all four inputs must be high.
    check_x_low_requires_all_high: assert property (
        @(posedge clk) (X == 1'b0) |-> (A_N & B & C & D)
    );

    // A low A_N forces X high.
    check_a_n_low_drives_x_high: assert property (
        @(posedge clk) (!A_N) |-> (X == 1'b1)
    );

    // A low B forces X high.
    check_b_low_drives_x_high: assert property (
        @(posedge clk) (!B) |-> (X == 1'b1)
    );

    // A low C forces X high.
    check_c_low_drives_x_high: assert property (
        @(posedge clk) (!C) |-> (X == 1'b1)
    );

    // A low D forces X high.
    check_d_low_drives_x_high: assert property (
        @(posedge clk) (!D) |-> (X == 1'b1)
    );

endmodule