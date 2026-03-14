module mux_2to1_sva (
    input logic CLK,       // sampling clock for assertions (DUT has no clock/reset)
    input logic [1:0] in,
    input logic sel,
    input logic out
);

    ///// Functional correctness /////
    // When sel=0, out equals in[0].
    check_sel0_function: assert property (
        @(posedge CLK) (sel === 1'b0) |-> (out == in[0])
    );

    // When sel=1, out equals in[1].
    check_sel1_function: assert property (
        @(posedge CLK) (sel === 1'b1) |-> (out == in[1])
    );

    // On sel rising edge, out equals in[1] at that time.
    check_on_sel_rise: assert property (
        @(posedge CLK) $rose(sel) |-> (out == in[1])
    );

    // On sel falling edge, out equals in[0] at that time.
    check_on_sel_fall: assert property (
        @(posedge CLK) $fell(sel) |-> (out == in[0])
    );

    // With stable inputs and select, output remains stable.
    check_output_stable_when_inputs_sel_stable: assert property (
        @(posedge CLK) ($stable(in) && $stable(sel)) |-> $stable(out)
    );

    // When both inputs are equal and sel is valid, out equals that value.
    check_equal_inputs: assert property (
        @(posedge CLK) ((in[0] == in[1]) && ((sel === 1'b0) || (sel === 1'b1))) |-> (out == in[0])
    );

    ///// Data dependence /////
    // If sel is stably 0 and in[0] changes, out must change.
    check_out_follows_in0_when_sel0: assert property (
        @(posedge CLK) (sel === 1'b0 && $past(sel) === 1'b0 && $changed(in[0])) |-> $changed(out)
    );

    // If sel is stably 1 and in[1] changes, out must change.
    check_out_follows_in1_when_sel1: assert property (
        @(posedge CLK) (sel === 1'b1 && $past(sel) === 1'b1 && $changed(in[1])) |-> $changed(out)
    );

    // If sel is stably 0, changes on in[1] alone do not affect out.
    check_out_ignores_in1_when_sel0: assert property (
        @(posedge CLK) (sel === 1'b0 && $past(sel) === 1'b0 && $changed(in[1]) && $stable(in[0])) |-> $stable(out)
    );

    // If sel is stably 1, changes on in[0] alone do not affect out.
    check_out_ignores_in0_when_sel1: assert property (
        @(posedge CLK) (sel === 1'b1 && $past(sel) === 1'b1 && $changed(in[0]) && $stable(in[1])) |-> $stable(out)
    );

endmodule