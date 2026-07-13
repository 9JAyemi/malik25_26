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

    // All three high inputs must drive Z high.
    check_all_inputs_high_drive_output_high: assert property (
        @(posedge clk) (A && B && C) |-> Z
    );

    // A low input must force Z low.
    check_a_low_forces_output_low: assert property (
        @(posedge clk) !A |-> !Z
    );

    // B low input must force Z low.
    check_b_low_forces_output_low: assert property (
        @(posedge clk) !B |-> !Z
    );

    // C low input must force Z low.
    check_c_low_forces_output_low: assert property (
        @(posedge clk) !C |-> !Z
    );

endmodule