module sky130_fd_sc_hd__o21bai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

// Y matches the implemented NAND/OR/NOT function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~(~B1_N & (A1 | A2))
    );

// A high B1_N forces Y high.
    check_b1n_high_forces_y_high: assert property (
        @(posedge clk) B1_N |-> Y
    );

// A low B1_N with both A inputs low forces Y high.
    check_a_inputs_low_force_y_high: assert property (
        @(posedge clk) (!B1_N && !A1 && !A2) |-> Y
    );

// A low B1_N with A1 low and A2 high forces Y low.
    check_a1_low_a2_high_forces_y_low: assert property (
        @(posedge clk) (!B1_N && !A1 && A2) |-> !Y
    );

// A low B1_N with A1 high and A2 low forces Y low.
    check_a1_high_a2_low_forces_y_low: assert property (
        @(posedge clk) (!B1_N && A1 && !A2) |-> !Y
    );

// A low B1_N with both A inputs high forces Y low.
    check_a_inputs_high_force_y_low: assert property (
        @(posedge clk) (!B1_N && A1 && A2) |-> !Y
    );

// A high Y requires B1_N to be high.
    check_y_high_requires_b1n_high: assert property (
        @(posedge clk) Y |-> B1_N
    );

// A high Y requires both A inputs low.
    check_y_high_requires_a_inputs_low: assert property (
        @(posedge clk) Y |-> (!A1 && !A2)
    );

// A low Y requires B1_N to be low.
    check_y_low_requires_b1n_low: assert property (
        @(posedge clk) !Y |-> !B1_N
    );

// A low Y requires at least one A input high.
    check_y_low_requires_a_inputs_high: assert property (
        @(posedge clk) !Y |-> (A1 || A2)
    );

endmodule
