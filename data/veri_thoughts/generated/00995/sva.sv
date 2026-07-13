module mux_2_1_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic SEL,
    input logic OUT
);
    ///// Functional equivalence /////
    // OUT implements (~SEL & A) | (SEL & B).
    check_functional_equation: assert property (
        @(posedge CLK) disable iff (1'b0) OUT == ((~SEL & A) | (SEL & B))
    );

    // When SEL=0, OUT equals A.
    check_sel0_drives_A: assert property (
        @(posedge CLK) disable iff (1'b0) (SEL == 1'b0) |-> (OUT == A)
    );

    // When SEL=1, OUT equals B.
    check_sel1_drives_B: assert property (
        @(posedge CLK) disable iff (1'b0) (SEL == 1'b1) |-> (OUT == B)
    );

    ///// Independence from unselected input /////
    // With SEL stable at 0, changes on B do not change OUT.
    check_out_independent_of_B_when_sel0: assert property (
        @(posedge CLK) disable iff (1'b0) (SEL == 1'b0 && $stable(SEL) && $changed(B)) |-> $stable(OUT)
    );

    // With SEL stable at 1, changes on A do not change OUT.
    check_out_independent_of_A_when_sel1: assert property (
        @(posedge CLK) disable iff (1'b0) (SEL == 1'b1 && $stable(SEL) && $changed(A)) |-> $stable(OUT)
    );

    ///// Tracking of selected input /////
    // With SEL stable at 0, changes on A cause OUT to change.
    check_out_tracks_A_when_sel0: assert property (
        @(posedge CLK) disable iff (1'b0) (SEL == 1'b0 && $stable(SEL) && $changed(A)) |-> $changed(OUT)
    );

    // With SEL stable at 1, changes on B cause OUT to change.
    check_out_tracks_B_when_sel1: assert property (
        @(posedge CLK) disable iff (1'b0) (SEL == 1'b1 && $stable(SEL) && $changed(B)) |-> $changed(OUT)
    );

    ///// Change attribution when select is stable /////
    // With SEL stable at 0, any OUT change is due to A changing.
    check_out_change_caused_by_A_when_sel0: assert property (
        @(posedge CLK) disable iff (1'b0) (SEL == 1'b0 && $stable(SEL) && $changed(OUT)) |-> $changed(A)
    );

    // With SEL stable at 1, any OUT change is due to B changing.
    check_out_change_caused_by_B_when_sel1: assert property (
        @(posedge CLK) disable iff (1'b0) (SEL == 1'b1 && $stable(SEL) && $changed(OUT)) |-> $changed(B)
    );

    ///// Stability relations /////
    // If A, B, and SEL are stable, OUT is stable.
    check_stable_inputs_imply_stable_out: assert property (
        @(posedge CLK) disable iff (1'b0) $stable({A,B,SEL}) |-> $stable(OUT)
    );

    ///// Select toggling effects /////
    // If A==B, toggling SEL does not change OUT.
    check_sel_toggle_same_inputs_no_out_change: assert property (
        @(posedge CLK) disable iff (1'b0) ($changed(SEL) && (A == B)) |-> $stable(OUT)
    );

    // If A!=B, toggling SEL changes OUT.
    check_sel_toggle_diff_inputs_change_out: assert property (
        @(posedge CLK) disable iff (1'b0) ($changed(SEL) && (A != B)) |-> $changed(OUT)
    );

endmodule