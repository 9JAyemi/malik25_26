module sky130_fd_sc_ms__o221a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // X matches the implemented O221A Boolean function.
    check_x_matches_o221a_function: assert property (
        @(posedge clk) X == (((B2 | B1) & (A2 | A1)) & C1)
    );

    // C1 low forces the output low.
    check_c1_low_forces_x_low: assert property (
        @(posedge clk) !C1 |-> !X
    );

    // If both A inputs are low, the output is low.
    check_a_inputs_low_force_x_low: assert property (
        @(posedge clk) !(A2 | A1) |-> !X
    );

    // If both B inputs are low, the output is low.
    check_b_inputs_low_force_x_low: assert property (
        @(posedge clk) !(B2 | B1) |-> !X
    );

    // A high output requires C1 and one A input and one B input high.
    check_x_high_requires_all_enables: assert property (
        @(posedge clk) X |-> (C1 && (A2 | A1) && (B2 | B1))
    );

    // C1 and one A input and one B input high drive the output high.
    check_all_enables_drive_x_high: assert property (
        @(posedge clk) (C1 && (A2 | A1) && (B2 | B1)) |-> X
    );

endmodule