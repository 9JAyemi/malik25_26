module sky130_fd_sc_ms__a2bb2o_sva (
    input logic clk,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic X
);

    // X must match the implemented combinational equation.
    check_x_function: assert property (
        @(posedge clk) X == ((~B1) | (~B2) | (A1_N & A2_N))
    );

    // If B1 is low, the shared B term is low and X must be high.
    check_x_high_when_b1_low: assert property (
        @(posedge clk) (!B1) |-> X
    );

    // If B2 is low, the shared B term is low and X must be high.
    check_x_high_when_b2_low: assert property (
        @(posedge clk) (!B2) |-> X
    );

    // With both B inputs high, an asserted A1 path forces X low.
    check_x_low_when_a1_path_active: assert property (
        @(posedge clk) (B1 & B2 & ~A1_N) |-> (!X)
    );

    // With both B inputs high, an asserted A2 path forces X low.
    check_x_low_when_a2_path_active: assert property (
        @(posedge clk) (B1 & B2 & ~A2_N) |-> (!X)
    );

    // With both B inputs high, inactive A paths keep X high.
    check_x_high_when_b_high_and_a_inactive: assert property (
        @(posedge clk) (B1 & B2 & A1_N & A2_N) |-> X
    );

    // A low X can only occur when both B inputs are high and some A path is active.
    check_x_low_implies_active_b_and_a_path: assert property (
        @(posedge clk) (!X) |-> (B1 & B2 & ((~A1_N) | (~A2_N)))
    );

    // If X is high while both B inputs are high, both A paths must be inactive.
    check_x_high_with_b_high_implies_a_inactive: assert property (
        @(posedge clk) (B1 & B2 & X) |-> (A1_N & A2_N)
    );

endmodule