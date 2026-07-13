module sky130_fd_sc_hd__nand3b_sva (
    input logic CLK,   // sampling clock for combinational checks
    input logic Y,
    input logic A_N,
    input logic B,
    input logic C
);
    ///// Functional correctness of NAND3B (Y = ~(B & C & ~A_N)) /////

    // Combinational truth: Y equals ~(B & C & ~A_N).
    check_truth_function: assert property (
        @(posedge CLK) Y == ~(B & C & ~A_N)
    );

    // Y is LOW only when B=1, C=1, and A_N=0.
    check_low_requires_all_inputs: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (B == 1'b1) && (C == 1'b1) && (A_N == 1'b0)
    );

    // When B=1, C=1, and A_N=0, Y must be LOW.
    check_all_inputs_force_low: assert property (
        @(posedge CLK) ((B == 1'b1) && (C == 1'b1) && (A_N == 1'b0)) |-> (Y == 1'b0)
    );

    // A_N=1 forces Y=1 (since ~A_N=0 makes the AND term 0).
    check_AN_high_forces_high: assert property (
        @(posedge CLK) (A_N == 1'b1) |-> (Y == 1'b1)
    );

    // B=0 forces Y=1 (NAND with a 0 input is 1).
    check_B_low_forces_high: assert property (
        @(posedge CLK) (B == 1'b0) |-> (Y == 1'b1)
    );

    // C=0 forces Y=1 (NAND with a 0 input is 1).
    check_C_low_forces_high: assert property (
        @(posedge CLK) (C == 1'b0) |-> (Y == 1'b1)
    );

    // With B=1 and C=1, Y equals A_N.
    check_BC_high_output_equals_AN: assert property (
        @(posedge CLK) ((B == 1'b1) && (C == 1'b1)) |-> (Y == A_N)
    );

    // With A_N=0, Y equals ~(B & C).
    check_AN_low_output_equals_nand_BC: assert property (
        @(posedge CLK) (A_N == 1'b0) |-> (Y == ~(B & C))
    );

endmodule