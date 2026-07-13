module mux_2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);

    // If all inputs are unchanged, the output must remain unchanged.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge clk)
        $stable(sel) && $stable(a) && $stable(b) |-> $stable(out)
    );

    // While sel is held low, a change on unselected input b must not affect out.
    check_b_ignored_when_sel_low: assert property (
        @(posedge clk)
        !sel && $stable(sel) && $stable(a) && $changed(b) |-> $stable(out)
    );

    // While sel is held high, a change on unselected input a must not affect out.
    check_a_ignored_when_sel_high: assert property (
        @(posedge clk)
        sel && $stable(sel) && $stable(b) && $changed(a) |-> $stable(out)
    );

    // After sel rises and b is held stable, out must reflect b on the next sample.
    check_sel_rise_selects_b_when_held: assert property (
        @(posedge clk)
        ($rose(sel) && $stable(a) && $stable(b)) ##1 (sel && $stable(b)) |-> (out == b)
    );

    // After sel falls and a is held stable, out must reflect a on the next sample.
    check_sel_fall_selects_a_when_held: assert property (
        @(posedge clk)
        ($fell(sel) && $stable(a) && $stable(b)) ##1 (!sel && $stable(a)) |-> (out == a)
    );

endmodule