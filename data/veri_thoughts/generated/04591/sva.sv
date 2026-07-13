module sky130_fd_sc_hd__o311a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);

    // X must match the implemented OR-AND logic.
    check_output_equation: assert property (
        @(posedge clk) X == ((A1 || A2 || A3) && B1 && C1)
    );

    // B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // C1 low forces X low.
    check_c1_low_forces_x_low: assert property (
        @(posedge clk) !C1 |-> !X
    );

    // If all A inputs are low, X must be low.
    check_all_a_low_forces_x_low: assert property (
        @(posedge clk) (!A1 && !A2 && !A3) |-> !X
    );

    // If any A is high with B1 and C1 high, X must be high.
    check_valid_high_condition: assert property (
        @(posedge clk) ((A1 || A2 || A3) && B1 && C1) |-> X
    );

    // A high X requires B1, C1, and at least one A input high.
    check_x_high_requires_valid_inputs: assert property (
        @(posedge clk) X |-> (B1 && C1 && (A1 || A2 || A3))
    );

endmodule