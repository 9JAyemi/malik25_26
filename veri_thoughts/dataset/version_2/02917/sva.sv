module mux_2to1_sva (
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic out_always
);
    // Output implements (sel_b1 && sel_b2) ? b : a.
    check_mux_function: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2 or posedge out_always or negedge out_always)
            out_always == ((sel_b1 && sel_b2) ? b : a)
    );

    // When both selects are HIGH, output equals b.
    check_b_selected: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2 or posedge out_always or negedge out_always)
            (sel_b1 && sel_b2) |-> (out_always == b)
    );

    // When selects are not both HIGH, output equals a.
    check_a_selected: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2 or posedge out_always or negedge out_always)
            (!(sel_b1 && sel_b2)) |-> (out_always == a)
    );

    // If output differs from a, both selects must be HIGH.
    check_not_a_implies_select_b: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2 or posedge out_always or negedge out_always)
            (out_always != a) |-> (sel_b1 && sel_b2)
    );

    // Changes on b are gated when not both selects HIGH (a stable).
    check_b_gated_when_not_selected: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2 or posedge out_always or negedge out_always)
            ((!sel_b1 || !sel_b2) && $stable(a) && $changed(b)) |-> $stable(out_always)
    );

    // With both selects HIGH, a-changes do not affect output (b stable).
    check_a_ignored_when_b_selected: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2 or posedge out_always or negedge out_always)
            ((sel_b1 && sel_b2) && $stable(b) && $changed(a)) |-> $stable(out_always)
    );

    // With both selects HIGH, output follows b on b changes (a stable).
    check_out_follows_b_when_selected: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2 or posedge out_always or negedge out_always)
            ((sel_b1 && sel_b2) && $stable(a) && $changed(b)) |-> $changed(out_always)
    );

    // With selects not both HIGH, output follows a on a changes (b stable).
    check_out_follows_a_when_not_selected: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2 or posedge out_always or negedge out_always)
            ((!sel_b1 || !sel_b2) && $stable(b) && $changed(a)) |-> $changed(out_always)
    );

    // Output equals either a or b at all times.
    check_output_is_a_or_b: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2 or posedge out_always or negedge out_always)
            (out_always == a) || (out_always == b)
    );

    // Any output change must be caused by a, b, or select changes.
    check_output_change_has_cause: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2 or posedge out_always or negedge out_always)
            $changed(out_always) |-> ($changed(a) || $changed(b) || $changed(sel_b1) || $changed(sel_b2))
    );
endmodule