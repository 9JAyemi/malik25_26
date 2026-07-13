module and_gate_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic X,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must equal the AND of A1, A2, B1, and VPWR.
    check_x_matches_and_function: assert property (
        @(posedge clk) X == (A1 & A2 & B1 & VPWR)
    );

    // X can be high only when all four AND inputs are high.
    check_x_high_requires_all_inputs_high: assert property (
        @(posedge clk) X |-> (A1 && A2 && B1 && VPWR)
    );

    // All four AND inputs high must drive X high.
    check_all_inputs_high_drive_x_high: assert property (
        @(posedge clk) (A1 && A2 && B1 && VPWR) |-> X
    );

    // A low A1 input must force X low.
    check_a1_low_forces_x_low: assert property (
        @(posedge clk) !A1 |-> !X
    );

    // A low A2 input must force X low.
    check_a2_low_forces_x_low: assert property (
        @(posedge clk) !A2 |-> !X
    );

    // A low B1 input must force X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // A low VPWR input must force X low.
    check_vpwr_low_forces_x_low: assert property (
        @(posedge clk) !VPWR |-> !X
    );

    // VGND, VPB, and VNB do not affect X when the AND inputs are stable.
    check_x_ignores_unused_inputs: assert property (
        @(posedge clk)
        ($stable(A1) && $stable(A2) && $stable(B1) && $stable(VPWR) &&
         $changed(VGND) && $stable(VPB) && $stable(VNB))
        |-> $stable(X)
    );

endmodule