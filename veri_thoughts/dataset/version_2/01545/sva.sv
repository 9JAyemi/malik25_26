module top_module_sva (
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic out_always
);
    // Sample on any edge of inputs (no clock/reset in RTL; combinational mux).
    // Output equals a whenever sel_b2 is 0.
    route_a_when_sel0: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        (sel_b2 == 1'b0) |-> (out_always == a)
    );
    // Output equals b whenever sel_b2 is 1.
    route_b_when_sel1: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        (sel_b2 == 1'b1) |-> (out_always == b)
    );
    // If selecting a and select is stable, any output change must be due to a changing.
    out_change_requires_a_when_sel0: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        ($stable(sel_b2) && (sel_b2 == 1'b0) && $changed(out_always)) |-> $changed(a)
    );
    // If selecting b and select is stable, any output change must be due to b changing.
    out_change_requires_b_when_sel1: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        ($stable(sel_b2) && (sel_b2 == 1'b1) && $changed(out_always)) |-> $changed(b)
    );
    // If selecting a and a changes with stable select, output must change to match a.
    a_change_updates_out_when_sel0: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        ($stable(sel_b2) && (sel_b2 == 1'b0) && $changed(a)) |-> ($changed(out_always) && (out_always == a))
    );
    // If selecting b and b changes with stable select, output must change to match b.
    b_change_updates_out_when_sel1: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        ($stable(sel_b2) && (sel_b2 == 1'b1) && $changed(b)) |-> ($changed(out_always) && (out_always == b))
    );
    // If a, b, and sel_b2 are stable, output must be stable.
    out_stable_if_inputs_and_select_stable: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        ($stable(a) && $stable(b) && $stable(sel_b2)) |-> $stable(out_always)
    );
    // Changing sel_b1 alone (with a, b, sel_b2 stable) must not affect the output.
    selb1_change_no_effect: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        ($changed(sel_b1) && $stable(a) && $stable(b) && $stable(sel_b2)) |-> $stable(out_always)
    );
    // On rising edge of sel_b2, output selects b.
    out_b_on_selb2_rise: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        $rose(sel_b2) |-> (out_always == b)
    );
    // On falling edge of sel_b2, output selects a.
    out_a_on_selb2_fall: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        $fell(sel_b2) |-> (out_always == a)
    );
endmodule