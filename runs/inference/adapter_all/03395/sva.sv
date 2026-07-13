module AND3_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Z
);

    // Z must equal the AND of A, B, and C.
    check_and_function: assert property (
        @(posedge clk) Z == (A & B & C)
    );

    // All inputs high must drive Z high.
    check_all_inputs_high_drive_z_high: assert property (
        @(posedge clk) (A && B && C) |-> Z
    );

    // A low must force Z low.
    check_a_low_forces_z_low: assert property (
        @(posedge clk) !A |-> !Z
    );

    // B low must force Z low.
    check_b_low_forces_z_low: assert property (
        @(posedge clk) !B |-> !Z
    );

    // C low must force Z low.
    check_c_low_forces_z_low: assert property (
        @(posedge clk) !C |-> !Z
    );

    // Z high requires all inputs high.
    check_z_high_requires_all_inputs_high: assert property (
        @(posedge clk) Z |-> (A && B && C)
    );

endmodule