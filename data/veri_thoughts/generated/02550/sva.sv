module sky130_fd_sc_hd__a21boi_sva (
    input  logic CLK,   // External property clock (DUT is combinational)
    input  logic Y,
    input  logic A1,
    input  logic A2,
    input  logic B1_N
);
    // No reset in DUT; assertions are always active.

    // Y implements B1_N & ~(A1 & A2).
    check_functional_equation: assert property (
        @(posedge CLK) Y == (B1_N & ~(A1 & A2))
    );

    // If B1_N is LOW, Y must be LOW.
    check_b1n_low_forces_y_low: assert property (
        @(posedge CLK) (!B1_N) |-> (Y == 1'b0)
    );

    // If both A1 and A2 are HIGH, Y must be LOW.
    check_a1a2_both_high_forces_y_low: assert property (
        @(posedge CLK) (A1 && A2) |-> (Y == 1'b0)
    );

    // When B1_N is HIGH, Y equals ~(A1 & A2).
    check_b1n_high_reduces_to_nand: assert property (
        @(posedge CLK) B1_N |-> (Y == ~(A1 & A2))
    );

    // If either A1 or A2 is LOW, Y equals B1_N.
    check_either_a_low_passes_b1n: assert property (
        @(posedge CLK) (!A1 || !A2) |-> (Y == B1_N)
    );

    // If Y is HIGH, then B1_N is HIGH and at least one of A1/A2 is LOW.
    check_y_high_implies_conditions: assert property (
        @(posedge CLK) (Y == 1'b1) |-> (B1_N && (!A1 || !A2))
    );

    // If Y is LOW, then B1_N is LOW or (A1 & A2) is HIGH.
    check_y_low_implies_causes: assert property (
        @(posedge CLK) (Y == 1'b0) |-> ((!B1_N) || (A1 && A2))
    );

    // If inputs hold their values, Y must hold its value as well.
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A1) && $stable(A2) && $stable(B1_N)) |-> $stable(Y)
    );

    // When path is enabled (!A1 || !A2) across cycles, Y changes iff B1_N changes.
    check_b1n_change_propagates_when_enabled: assert property (
        @(posedge CLK) ($past(!A1 || !A2) && (!A1 || !A2) && $changed(B1_N)) |-> $changed(Y)
    );

    // With B1_N HIGH, a 0->1 transition on (A1 & A2) forces Y LOW.
    check_rise_a1and_a2_forces_y_low_when_b1n_high: assert property (
        @(posedge CLK) (B1_N && $rose(A1 && A2)) |-> (Y == 1'b0)
    );

endmodule