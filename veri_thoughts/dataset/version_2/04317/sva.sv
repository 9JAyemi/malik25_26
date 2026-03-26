module sky130_fd_sc_hdll__o211a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X matches the implemented O211A logic equation.
    check_output_equation: assert property (
        @(posedge clk) X === ((A1 | A2) & B1 & C1)
    );

    // B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) (B1 === 1'b0) |-> (X === 1'b0)
    );

    // C1 low forces X low.
    check_c1_low_forces_x_low: assert property (
        @(posedge clk) (C1 === 1'b0) |-> (X === 1'b0)
    );

    // Both A inputs low force X low.
    check_a_inputs_low_force_x_low: assert property (
        @(posedge clk) ((A1 === 1'b0) && (A2 === 1'b0)) |-> (X === 1'b0)
    );

    // High X requires both B1 and C1 high.
    check_x_high_requires_b1_and_c1: assert property (
        @(posedge clk) (X === 1'b1) |-> ((B1 === 1'b1) && (C1 === 1'b1))
    );

    // High X requires at least one A input high.
    check_x_high_requires_a1_or_a2: assert property (
        @(posedge clk) (X === 1'b1) |-> ((A1 === 1'b1) || (A2 === 1'b1))
    );

    // A1 can drive X high when B1 and C1 are high.
    check_a1_path_drives_x_high: assert property (
        @(posedge clk) ((A1 === 1'b1) && (B1 === 1'b1) && (C1 === 1'b1)) |-> (X === 1'b1)
    );

    // A2 can drive X high when B1 and C1 are high.
    check_a2_path_drives_x_high: assert property (
        @(posedge clk) ((A2 === 1'b1) && (B1 === 1'b1) && (C1 === 1'b1)) |-> (X === 1'b1)
    );

endmodule