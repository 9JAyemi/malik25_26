module AND4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Z
);

    // Z must equal the AND of all four inputs.
    check_output_matches_and4: assert property (
        @(posedge clk) Z == (A & B & C & D)
    );

    // All inputs high must drive Z high.
    check_all_inputs_high_drive_output_high: assert property (
        @(posedge clk) (A & B & C & D) |-> Z
    );

    // A low must force Z low.
    check_a_low_forces_output_low: assert property (
        @(posedge clk) !A |-> !Z
    );

    // B low must force Z low.
    check_b_low_forces_output_low: assert property (
        @(posedge clk) !B |-> !Z
    );

    // C low must force Z low.
    check_c_low_forces_output_low: assert property (
        @(posedge clk) !C |-> !Z
    );

    // D low must force Z low.
    check_d_low_forces_output_low: assert property (
        @(posedge clk) !D |-> !Z
    );

    // Z high requires all inputs high.
    check_output_high_requires_all_inputs_high: assert property (
        @(posedge clk) Z |-> (A & B & C & D)
    );

endmodule