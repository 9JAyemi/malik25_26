module sky130_fd_sc_lp__or2b_2_sva (
    input logic CLK,
    input logic X,
    input logic A,
    input logic B_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // X equals A OR NOT B_N.
    check_function_equivalence: assert property (
        @(posedge CLK) X == (A | ~B_N)
    );

    // When B_N is 1, X equals A.
    check_bn1_implies_x_eq_a: assert property (
        @(posedge CLK) (B_N == 1'b1) |-> (X == A)
    );

    // When B_N is 0, X is 1.
    check_bn0_forces_x_high: assert property (
        @(posedge CLK) (B_N == 1'b0) |-> (X == 1'b1)
    );

    // When A is 1, X is 1.
    check_a1_forces_x_high: assert property (
        @(posedge CLK) (A == 1'b1) |-> (X == 1'b1)
    );

    // When A is 0 and B_N is 1, X is 0.
    check_a0_bn1_forces_x_low: assert property (
        @(posedge CLK) ((A == 1'b0) && (B_N == 1'b1)) |-> (X == 1'b0)
    );

    // If A and B_N are stable, X remains stable.
    check_output_stability_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B_N)) |-> $stable(X)
    );

    // Changes on VPWR do not affect X when A and B_N are stable.
    check_vpwr_changes_do_not_affect_x: assert property (
        @(posedge CLK) ($changed(VPWR) && $stable(A) && $stable(B_N)) |-> $stable(X)
    );

    // Changes on VGND do not affect X when A and B_N are stable.
    check_vgnd_changes_do_not_affect_x: assert property (
        @(posedge CLK) ($changed(VGND) && $stable(A) && $stable(B_N)) |-> $stable(X)
    );

    // Changes on VPB do not affect X when A and B_N are stable.
    check_vpb_changes_do_not_affect_x: assert property (
        @(posedge CLK) ($changed(VPB) && $stable(A) && $stable(B_N)) |-> $stable(X)
    );

    // Changes on VNB do not affect X when A and B_N are stable.
    check_vnb_changes_do_not_affect_x: assert property (
        @(posedge CLK) ($changed(VNB) && $stable(A) && $stable(B_N)) |-> $stable(X)
    );
endmodule