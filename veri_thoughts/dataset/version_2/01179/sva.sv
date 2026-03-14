module top_module_sva (
    input logic CLK,
    input logic a,
    input logic b,
    input logic sel,
    input logic [1:0] diff
);
    // diff bits must be equal.
    check_diff_bits_equal: assert property (
        @(posedge CLK) (diff[1] == diff[0])
    );

    // diff can only be 2'b00 or 2'b11.
    check_diff_limited_values: assert property (
        @(posedge CLK) (diff inside {2'b00, 2'b11})
    );

    // Functional equivalence: diff == {2{~(sel ? b : a)}}.
    check_diff_functional_equiv: assert property (
        @(posedge CLK) (diff == {2{~(sel ? b : a)}})
    );

    // When sel=0, diff depends only on a.
    check_when_sel0: assert property (
        @(posedge CLK) (sel == 1'b0) |-> (diff == {2{~a}})
    );

    // When sel=1, diff depends only on b.
    check_when_sel1: assert property (
        @(posedge CLK) (sel == 1'b1) |-> (diff == {2{~b}})
    );

    // If inputs a,b,sel are stable, diff is stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({a,b,sel}) |-> $stable(diff)
    );

    // With sel=0, if only a changes, diff changes.
    check_selected_a_change_affects_diff: assert property (
        @(posedge CLK) (sel==1'b0 && $stable(sel) && $stable(b) && $changed(a)) |-> $changed(diff)
    );

    // With sel=1, if only b changes, diff changes.
    check_selected_b_change_affects_diff: assert property (
        @(posedge CLK) (sel==1'b1 && $stable(sel) && $stable(a) && $changed(b)) |-> $changed(diff)
    );

    // With sel=0, if only b changes, diff is stable.
    check_unselected_b_change_no_effect: assert property (
        @(posedge CLK) (sel==1'b0 && $stable(sel) && $stable(a) && $changed(b)) |-> $stable(diff)
    );

    // With sel=1, if only a changes, diff is stable.
    check_unselected_a_change_no_effect: assert property (
        @(posedge CLK) (sel==1'b1 && $stable(sel) && $stable(b) && $changed(a)) |-> $stable(diff)
    );
endmodule