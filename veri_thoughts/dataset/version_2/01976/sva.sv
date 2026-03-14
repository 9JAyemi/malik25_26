module sky130_fd_sc_lp__a22o_m_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Notes: No clock/reset in RTL; pure combinational. Sample assertions on posedge VPWR.
    ///// Functional correctness: X = (A1 & A2) & (B1 & B2) /////
    // X equals logical AND of all four inputs.
    check_func_equiv_and4: assert property (
        @(posedge VPWR) X === (A1 & A2 & B1 & B2)
    );

    ///// Basic implications /////
    // If X is HIGH, all inputs must be HIGH.
    check_x_high_implies_all_high: assert property (
        @(posedge VPWR) X |-> (A1 && A2 && B1 && B2)
    );
    // If all inputs are HIGH, X must be HIGH.
    check_all_high_implies_x_high: assert property (
        @(posedge VPWR) (A1 && A2 && B1 && B2) |-> (X == 1'b1)
    );

    ///// Each input low forces X low /////
    // A1 LOW forces X LOW.
    check_a1_low_forces_x_low: assert property (
        @(posedge VPWR) (!A1) |-> (X == 1'b0)
    );
    // A2 LOW forces X LOW.
    check_a2_low_forces_x_low: assert property (
        @(posedge VPWR) (!A2) |-> (X == 1'b0)
    );
    // B1 LOW forces X LOW.
    check_b1_low_forces_x_low: assert property (
        @(posedge VPWR) (!B1) |-> (X == 1'b0)
    );
    // B2 LOW forces X LOW.
    check_b2_low_forces_x_low: assert property (
        @(posedge VPWR) (!B2) |-> (X == 1'b0)
    );

    ///// Temporal consistency /////
    // If inputs are stable across samples, X is stable.
    check_stable_inputs_stable_x: assert property (
        @(posedge VPWR) $stable({A1,A2,B1,B2}) |-> $stable(X)
    );
    // X can change only if at least one input changed.
    check_x_change_requires_input_change: assert property (
        @(posedge VPWR) $changed(X) |-> ($changed(A1) || $changed(A2) || $changed(B1) || $changed(B2))
    );
    // If X falls, then not all inputs are HIGH at that sample.
    check_fall_x_requires_not_all_high: assert property (
        @(posedge VPWR) $fell(X) |-> !(A1 && A2 && B1 && B2)
    );

endmodule