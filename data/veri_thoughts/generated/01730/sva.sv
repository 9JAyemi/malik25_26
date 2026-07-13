module mux2to1_sva (
    input logic CLK,
    input logic in0,
    input logic in1,
    input logic sel,
    input logic out
);
    // Out equals selected input per mux function.
    check_mux_function: assert property (
        @(posedge CLK) out == (sel ? in1 : in0)
    );

    // When sel=0, out mirrors in0.
    check_sel0_path: assert property (
        @(posedge CLK) (sel == 1'b0) |-> (out == in0)
    );

    // When sel=1, out mirrors in1.
    check_sel1_path: assert property (
        @(posedge CLK) (sel == 1'b1) |-> (out == in1)
    );

    // If in0,in1,sel are unchanged across cycles, out is unchanged.
    check_out_stable_if_inputs_stable: assert property (
        @(posedge CLK) (!$changed(in0) && !$changed(in1) && !$changed(sel)) |-> !$changed(out)
    );

    // With sel stable 0, out changes only if in0 changes.
    check_out_change_requires_in0_when_sel0: assert property (
        @(posedge CLK) (sel == 1'b0 && $past(sel) == 1'b0 && $changed(out)) |-> $changed(in0)
    );

    // With sel stable 1, out changes only if in1 changes.
    check_out_change_requires_in1_when_sel1: assert property (
        @(posedge CLK) (sel == 1'b1 && $past(sel) == 1'b1 && $changed(out)) |-> $changed(in1)
    );

    // With sel stable 0 and in0 unchanged, out is unchanged.
    check_out_stable_sel0_if_in0_stable: assert property (
        @(posedge CLK) (sel == 1'b0 && $past(sel) == 1'b0 && !$changed(in0)) |-> !$changed(out)
    );

    // With sel stable 1 and in1 unchanged, out is unchanged.
    check_out_stable_sel1_if_in1_stable: assert property (
        @(posedge CLK) (sel == 1'b1 && $past(sel) == 1'b1 && !$changed(in1)) |-> !$changed(out)
    );
endmodule