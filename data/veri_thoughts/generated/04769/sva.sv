module sky130_fd_sc_hd__o2bb2a_sva (
    input logic clk,
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // X matches the implemented NAND/OR/AND logic.
    check_output_function: assert property (
        @(posedge clk)
        X == ((~(A1_N & A2_N)) & (B1 | B2))
    );

    // If both B inputs are low, X must be low.
    check_b_inputs_force_low: assert property (
        @(posedge clk)
        (!B1 && !B2) |-> !X
    );

    // If both A inputs are high, the NAND term is low and X must be low.
    check_a_inputs_force_low: assert property (
        @(posedge clk)
        (A1_N && A2_N) |-> !X
    );

    // If A1_N is low and either B input is high, X must be high.
    check_a1_low_with_b_high_sets_x: assert property (
        @(posedge clk)
        (!A1_N && (B1 || B2)) |-> X
    );

    // If A2_N is low and either B input is high, X must be high.
    check_a2_low_with_b_high_sets_x: assert property (
        @(posedge clk)
        (!A2_N && (B1 || B2)) |-> X
    );

    // A high X requires at least one B input to be high.
    check_x_high_requires_b_high: assert property (
        @(posedge clk)
        X |-> (B1 || B2)
    );

    // A high X requires at least one A input to be low.
    check_x_high_requires_a_low: assert property (
        @(posedge clk)
        X |-> (!A1_N || !A2_N)
    );

endmodule