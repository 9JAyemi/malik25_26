module mux4to1_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic sel0,
    input logic sel1,
    input logic out
);

    // Output must match the mux select expression.
    check_mux_function: assert property (
        @(posedge clk)
        out == ((sel1 & sel0) ? in3 :
                (sel1 & ~sel0) ? in2 :
                (~sel1 & sel0) ? in1 :
                in0)
    );

    // When both select bits are high, output must come from in3.
    check_select_11: assert property (
        @(posedge clk)
        (sel1 && sel0) |-> (out == in3)
    );

    // When select bits differ, output must come from in2.
    check_select_mismatch: assert property (
        @(posedge clk)
        (sel1 ^ sel0) |-> (out == in2)
    );

    // When both select bits are low, output must come from in0.
    check_select_00: assert property (
        @(posedge clk)
        (!sel1 && !sel0) |-> (out == in0)
    );

    // With select bits held low and in0 stable, a change on in1 must not affect out.
    check_in1_ignored_when_00: assert property (
        @(posedge clk)
        (!sel1 && !sel0 && $stable(sel1) && $stable(sel0) && $stable(in0) && $changed(in1)) |-> $stable(out)
    );

    // With select bits held low and in0 stable, a change on in2 must not affect out.
    check_in2_ignored_when_00: assert property (
        @(posedge clk)
        (!sel1 && !sel0 && $stable(sel1) && $stable(sel0) && $stable(in0) && $changed(in2)) |-> $stable(out)
    );

    // With select bits held low and in0 stable, a change on in3 must not affect out.
    check_in3_ignored_when_00: assert property (
        @(posedge clk)
        (!sel1 && !sel0 && $stable(sel1) && $stable(sel0) && $stable(in0) && $changed(in3)) |-> $stable(out)
    );

    // With select bits held high and in3 stable, a change on in1 must not affect out.
    check_in1_ignored_when_11: assert property (
        @(posedge clk)
        (sel1 && sel0 && $stable(sel1) && $stable(sel0) && $stable(in3) && $changed(in1)) |-> $stable(out)
    );

    // With select bits held high and in3 stable, a change on in2 must not affect out.
    check_in2_ignored_when_11: assert property (
        @(posedge clk)
        (sel1 && sel0 && $stable(sel1) && $stable(sel0) && $stable(in3) && $changed(in2)) |-> $stable(out)
    );

    // With select bits held high and in3 stable, a change on in0 must not affect out.
    check_in0_ignored_when_11: assert property (
        @(posedge clk)
        (sel1 && sel0 && $stable(sel1) && $stable(sel0) && $stable(in3) && $changed(in0)) |-> $stable(out)
    );

    // With select bits held low and in0 stable, a change on in1 must not affect out.
    check_in1_ignored_when_01: assert property (
        @(posedge clk)
        (!sel1 && sel0 && $stable(sel1) && $stable(sel0) && $stable(in0) && $changed(in1)) |-> $stable(out)
    );

    // With select bits held low and in0 stable, a change on in2 must not affect out.
    check_in2_ignored_when_01: assert property (
        @(posedge clk)
        (!sel1 && sel0 && $stable(sel1) && $stable(sel0) && $stable(in0) && $changed(in2)) |-> $stable(out)
    );

    // With select bits held low and in0 stable, a change on in3 must not affect out.
    check_in3_ignored_when_01: assert property (
        @(posedge clk)
        (!sel1 && sel0 && $stable(sel1) && $stable(sel0) && $stable(in0) && $changed(in3)) |-> $stable(out)
    );

endmodule