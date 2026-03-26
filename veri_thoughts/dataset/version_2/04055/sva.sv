module buffer_3input_sva (
    input logic clk,
    input logic Z,
    input logic A,
    input logic B,
    input logic C,
    input logic TE_B
);

    // Z matches the implemented combinational equation.
    check_output_equation: assert property (
        @(posedge clk) Z == (TE_B & (A | B | C) & ~(A & B & C))
    );

    // TE_B low forces Z low.
    check_teb_low_forces_z_low: assert property (
        @(posedge clk) (TE_B == 1'b0) |-> (Z == 1'b0)
    );

    // All-zero inputs force Z low.
    check_all_zero_inputs_force_z_low: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0) && (C == 1'b0)) |-> (Z == 1'b0)
    );

    // All-one inputs force Z low.
    check_all_one_inputs_force_z_low: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b1) && (C == 1'b1)) |-> (Z == 1'b0)
    );

    // With TE_B high, mixed data inputs drive Z high.
    check_enabled_mixed_inputs_force_z_high: assert property (
        @(posedge clk)
        ((TE_B == 1'b1) && ((A | B | C) == 1'b1) && ((A & B & C) == 1'b0))
        |-> (Z == 1'b1)
    );

    // A high output requires TE_B to be high.
    check_z_requires_teb_high: assert property (
        @(posedge clk) (Z == 1'b1) |-> (TE_B == 1'b1)
    );

    // A high output requires inputs to be neither all-zero nor all-one.
    check_z_requires_mixed_inputs: assert property (
        @(posedge clk) (Z == 1'b1) |-> (((A | B | C) == 1'b1) && ((A & B & C) == 1'b0))
    );

endmodule