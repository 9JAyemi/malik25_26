module sky130_fd_sc_ls__o2111a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

// X matches the implemented O2111A Boolean function.
    check_functional_equivalence: assert property (
        @(posedge clk) X == (B1 & C1 & D1 & (A1 | A2))
    );

// A high X requires all four AND inputs to be high.
    check_x_high_requires_and_inputs: assert property (
        @(posedge clk) X |-> (B1 & C1 & D1)
    );

// A high X requires at least one OR input to be high.
    check_x_high_requires_or_input: assert property (
        @(posedge clk) X |-> (A1 | A2)
    );

// All four AND inputs high with at least one OR input high drive X high.
    check_all_conditions_drive_x_high: assert property (
        @(posedge clk) (B1 & C1 & D1 & (A1 | A2)) |-> X
    );

// A low B1 forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

// A low C1 forces X low.
    check_c1_low_forces_x_low: assert property (
        @(posedge clk) !C1 |-> !X
    );

// A low D1 forces X low.
    check_d1_low_forces_x_low: assert property (
        @(posedge clk) !D1 |-> !X
    );

// A low A1 with A2 low forces X low.
    check_a1_a2_low_forces_x_low: assert property (
        @(posedge clk) (!A1 && !A2) |-> !X
    );

endmodule
