module mux_2to1_sva (
    input logic out,
    input logic in0,
    input logic in1,
    input logic sel
);
    // No explicit clock/reset; behavior updates only on sel edges (posedge/negedge).
    // Function: on sel==0 capture in0; on sel==1 capture in1; out changes only when sel toggles.

    // Before update at a rising sel edge, out equals the previously latched in0.
    check_prev_latch_visible_on_rise: assert property (
        @(posedge sel or negedge sel) $rose(sel) |-> (out == $past(in0))
    );

    // Before update at a falling sel edge, out equals the previously latched in1.
    check_prev_latch_visible_on_fall: assert property (
        @(posedge sel or negedge sel) $fell(sel) |-> (out == $past(in1))
    );

    // After a rising sel edge, by the next sel edge out equals in1 captured at the rise.
    check_latch_in1_persists_until_next_edge: assert property (
        @(posedge sel or negedge sel) $rose(sel) |-> ##1 (out == $past(in1))
    );

    // After a falling sel edge, by the next sel edge out equals in0 captured at the fall.
    check_latch_in0_persists_until_next_edge: assert property (
        @(posedge sel or negedge sel) $fell(sel) |-> ##1 (out == $past(in0))
    );
endmodule