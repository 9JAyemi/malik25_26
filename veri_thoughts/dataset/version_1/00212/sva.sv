module my_and4_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic clk
);

    // When VPB is low, X is the 4-input AND of A through D.
    check_and_mode_function: assert property (
        @(posedge clk) (VPB == 1'b0) |-> (X == (A & B & C & D))
    );

    // When VPB is high, X is the 4-input OR of A through D.
    check_or_mode_function: assert property (
        @(posedge clk) (VPB == 1'b1) |-> (X == (A | B | C | D))
    );

    // In AND mode, all high inputs force X high.
    check_and_mode_all_inputs_high: assert property (
        @(posedge clk) (VPB == 1'b0 && A && B && C && D) |-> (X == 1'b1)
    );

    // In OR mode, all low inputs force X low.
    check_or_mode_all_inputs_low: assert property (
        @(posedge clk) (VPB == 1'b1 && !A && !B && !C && !D) |-> (X == 1'b0)
    );

    // With A, B, C, D, and VPB stable, X must remain stable.
    check_output_stable_when_functional_inputs_stable: assert property (
        @(posedge clk) $stable({A, B, C, D, VPB}) |-> $stable(X)
    );

    // A change on VPWR alone does not affect X.
    check_vpwr_change_no_effect: assert property (
        @(posedge clk) ($changed(VPWR) && $stable({A, B, C, D, VPB, VGND, VNB})) |-> $stable(X)
    );

    // A change on VGND alone does not affect X.
    check_vgnd_change_no_effect: assert property (
        @(posedge clk) ($changed(VGND) && $stable({A, B, C, D, VPB, VPWR, VNB})) |-> $stable(X)
    );

    // A change on VNB alone does not affect X.
    check_vnb_change_no_effect: assert property (
        @(posedge clk) ($changed(VNB) && $stable({A, B, C, D, VPB, VPWR, VGND})) |-> $stable(X)
    );

endmodule