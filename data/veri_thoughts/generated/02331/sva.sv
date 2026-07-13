module mux_2to1_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic sel,
    input logic out
);
    // Out equals selected input per mux function.
    check_mux_function: assert property (
        @(posedge CLK) out == ((sel == 1'b0) ? A : B)
    );

    // When sel is 0, out equals A.
    check_sel0_routes_A: assert property (
        @(posedge CLK) (sel == 1'b0) |-> (out == A)
    );

    // When sel is 1, out equals B.
    check_sel1_routes_B: assert property (
        @(posedge CLK) (sel == 1'b1) |-> (out == B)
    );

    // With sel=0 and stable sel/A, a change on B does not change out.
    check_out_independent_of_B_when_sel0: assert property (
        @(posedge CLK) (sel == 1'b0) && $stable(sel) && $stable(A) && $changed(B) |-> $stable(out)
    );

    // With sel=1 and stable sel/B, a change on A does not change out.
    check_out_independent_of_A_when_sel1: assert property (
        @(posedge CLK) (sel == 1'b1) && $stable(sel) && $stable(B) && $changed(A) |-> $stable(out)
    );

    // With stable sel=0, any out change must be due to A changing.
    check_out_change_caused_by_A_when_sel0: assert property (
        @(posedge CLK) (sel == 1'b0) && $stable(sel) && $changed(out) |-> $changed(A)
    );

    // With stable sel=1, any out change must be due to B changing.
    check_out_change_caused_by_B_when_sel1: assert property (
        @(posedge CLK) (sel == 1'b1) && $stable(sel) && $changed(out) |-> $changed(B)
    );

    // If sel, A, and B are all stable, out must be stable.
    check_out_stable_when_inputs_and_sel_stable: assert property (
        @(posedge CLK) $stable(sel) && $stable(A) && $stable(B) |-> $stable(out)
    );

    // If sel toggles while A==B and both stable, out must not change.
    check_sel_toggle_no_effect_when_AeqB: assert property (
        @(posedge CLK) $changed(sel) && $stable(A) && $stable(B) && (A == B) |-> $stable(out)
    );
endmodule