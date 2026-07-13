module top_module_sva (
    input logic CLK,          // Sampling clock for assertions (DUT has no clock/reset)
    input logic [3:0] A,      // DUT input
    input logic [3:0] B,      // DUT input
    input logic sel,          // DUT input
    input logic [3:0] OUT     // DUT output
);

    ///// Combinational functionality checks /////
    // OUT matches mux of two's complement of A vs B.
    check_mux_function: assert property (
        @(posedge CLK) OUT == (sel ? ((~A) + 4'b0001) : B)
    );

    // When sel=1, OUT is two's complement of A.
    check_sel1_twos_comp: assert property (
        @(posedge CLK) sel |-> (OUT == ((~A) + 4'b0001))
    );

    // When sel=0, OUT equals B.
    check_sel0_passthrough: assert property (
        @(posedge CLK) !sel |-> (OUT == B)
    );

    // When sel=1, A + OUT wraps to zero (4-bit two's complement identity).
    check_sel1_adds_to_zero: assert property (
        @(posedge CLK) sel |-> ((A + OUT) == 4'b0000)
    );

    // When sel=1 and A==0, OUT==0.
    check_sel1_zero_case: assert property (
        @(posedge CLK) (sel && (A == 4'b0000)) |-> (OUT == 4'b0000)
    );

    // When sel=1 and A==4'b1000, OUT==4'b1000 (min value is self-complement).
    check_sel1_min_value_fixed_point: assert property (
        @(posedge CLK) (sel && (A == 4'b1000)) |-> (OUT == 4'b1000)
    );

    // If B equals two's complement of A, OUT equals that value regardless of sel.
    check_equal_paths_agree: assert property (
        @(posedge CLK) (B == ((~A) + 4'b0001)) |-> (OUT == B)
    );

    ///// Sensitivity and stability /////
    // If only sel toggles while A and B are stable and the two paths differ, OUT must change.
    check_sel_toggle_updates_out: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && (B != ((~A) + 4'b0001)) && ($rose(sel) || $fell(sel))) |-> $changed(OUT)
    );

    // With sel held high across cycles, a change on A must change OUT.
    check_A_change_prop_to_out_when_sel1: assert property (
        @(posedge CLK) ($past(sel) && sel && $changed(A)) |-> $changed(OUT)
    );

    // With sel held low across cycles, a change on B must change OUT.
    check_B_change_prop_to_out_when_sel0: assert property (
        @(posedge CLK) (!$past(sel) && !sel && $changed(B)) |-> $changed(OUT)
    );

    // If A, B, and sel are all stable, OUT must be stable.
    check_quiescent_stability: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(sel)) |-> $stable(OUT)
    );

endmodule