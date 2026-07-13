module mux32_sva (
    input logic clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic sel,
    input logic [31:0] out
);
    // Mux function: out equals selected input every cycle.
    check_mux_function: assert property (
        @(posedge clk) out == (sel ? b : a)
    );

    // When sel is 0, out equals a.
    check_sel0_path: assert property (
        @(posedge clk) (!sel) |-> (out == a)
    );

    // When sel is 1, out equals b.
    check_sel1_path: assert property (
        @(posedge clk) (sel) |-> (out == b)
    );

    // If a, b, and sel hold their values, out must hold.
    check_stability_when_inputs_hold: assert property (
        @(posedge clk) ($stable(a) && $stable(b) && $stable(sel)) |-> $stable(out)
    );

    // An out change must be caused by sel change or selected input change.
    check_out_change_has_cause: assert property (
        @(posedge clk) $changed(out) |-> ($changed(sel) || (sel ? $changed(b) : $changed(a)))
    );

    // With sel=0 and a,sel stable, out is stable (insensitive to b).
    check_stable_out_sel0_when_a_and_sel_stable: assert property (
        @(posedge clk) (!sel && $stable(a) && $stable(sel)) |-> $stable(out)
    );

    // With sel=1 and b,sel stable, out is stable (insensitive to a).
    check_stable_out_sel1_when_b_and_sel_stable: assert property (
        @(posedge clk) (sel && $stable(b) && $stable(sel)) |-> $stable(out)
    );

    // If inputs are equal, out equals that value regardless of sel.
    check_equal_inputs_drive_out: assert property (
        @(posedge clk) (a == b) |-> (out == a)
    );

    // If sel stays 0 and a changes, out changes to match a.
    check_a_change_reflects_out_when_sel0: assert property (
        @(posedge clk) (!sel && !$past(sel) && (a != $past(a))) |-> ((out != $past(out)) && (out == a))
    );

    // If sel stays 1 and b changes, out changes to match b.
    check_b_change_reflects_out_when_sel1: assert property (
        @(posedge clk) (sel && $past(sel) && (b != $past(b))) |-> ((out != $past(out)) && (out == b))
    );

    // On sel rising edge with stable inputs, out selects b.
    check_out_switches_to_b_on_sel_rise: assert property (
        @(posedge clk) ($rose(sel) && $stable(a) && $stable(b)) |-> (out == b)
    );

    // On sel falling edge with stable inputs, out selects a.
    check_out_switches_to_a_on_sel_fall: assert property (
        @(posedge clk) ($fell(sel) && $stable(a) && $stable(b)) |-> (out == a)
    );
endmodule