module sky130_fd_sc_hdll__nand4b_sva (
    input logic CLK,
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);
    // DUT sky130_fd_sc_hdll__nand4b has no clock/reset; pure combinational. Sample on external CLK.
    // Y implements Y = ~(B & C & D & ~A_N) = A_N | ~B | ~C | ~D.

    // Y must equal the NAND4b Boolean function.
    check_functional_equivalence: assert property (
        @(posedge CLK) Y == ~(B & C & D & ~A_N)
    );

    // Y low only when B=C=D=1 and A_N=0.
    check_only_low_when_all_ones_A_N_low: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (B && C && D && ~A_N)
    );

    // When B=C=D=1 and A_N=0, Y must be low.
    check_low_when_all_ones_A_N_low_sufficient: assert property (
        @(posedge CLK) (B && C && D && ~A_N) |-> (Y == 1'b0)
    );

    // A_N high forces Y high.
    check_A_N_high_forces_one: assert property (
        @(posedge CLK) A_N |-> (Y == 1'b1)
    );

    // B low forces Y high.
    check_B_zero_forces_one: assert property (
        @(posedge CLK) (!B) |-> (Y == 1'b1)
    );

    // C low forces Y high.
    check_C_zero_forces_one: assert property (
        @(posedge CLK) (!C) |-> (Y == 1'b1)
    );

    // D low forces Y high.
    check_D_zero_forces_one: assert property (
        @(posedge CLK) (!D) |-> (Y == 1'b1)
    );

    // If Y is high, at least one of A_N or ~B or ~C or ~D is true.
    check_Y_high_implies_cause: assert property (
        @(posedge CLK) (Y == 1'b1) |-> (A_N || !B || !C || !D)
    );

    // When B=C=D=1, Y equals A_N.
    check_when_BCD_all_ones_output_equals_A_N: assert property (
        @(posedge CLK) (B && C && D) |-> (Y == A_N)
    );

    // When A_N=0 and B=C=1, Y equals ~D.
    check_when_AN_low_BC_ones_output_equals_notD: assert property (
        @(posedge CLK) (~A_N && B && C) |-> (Y == !D)
    );

endmodule