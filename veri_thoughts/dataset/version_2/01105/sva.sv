module mux_2to1_sva (
    input logic CLK,
    input logic RESETn,
    input logic out,
    input logic in0,
    input logic in1,
    input logic sel
);
    // Out equals the selected input each cycle.
    check_mux_function: assert property (
        @(posedge CLK) disable iff (!RESETn) out == (sel ? in1 : in0)
    );

    // When sel=0 and in0/sel are stable, a change on in1 does not change out.
    unselected_in1_no_effect_sel0: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel==1'b0 && $stable(sel) && $stable(in0) && $changed(in1)) |-> $stable(out)
    );

    // When sel=1 and in1/sel are stable, a change on in0 does not change out.
    unselected_in0_no_effect_sel1: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel==1'b1 && $stable(sel) && $stable(in1) && $changed(in0)) |-> $stable(out)
    );

    // If out changes, the cause is either sel changed or the selected input changed.
    out_change_has_valid_cause: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(out) |-> ($changed(sel) || (sel ? $changed(in1) : $changed(in0)))
    );

    // With sel=0 stable, any change on out must be due to in0 changing.
    out_change_caused_by_in0_when_sel0: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel==1'b0 && $stable(sel) && $changed(out)) |-> $changed(in0)
    );

    // With sel=1 stable, any change on out must be due to in1 changing.
    out_change_caused_by_in1_when_sel1: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel==1'b1 && $stable(sel) && $changed(out)) |-> $changed(in1)
    );

    // If inputs are equal, out equals that value regardless of sel.
    equal_inputs_bypass_sel: assert property (
        @(posedge CLK) disable iff (!RESETn) (in0 == in1) |-> (out == in0)
    );

    // With sel=0 stable, a rising edge on in0 causes a rising edge on out.
    track_rise_sel0: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel==1'b0 && $stable(sel) && $rose(in0)) |-> $rose(out)
    );

    // With sel=0 stable, a falling edge on in0 causes a falling edge on out.
    track_fall_sel0: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel==1'b0 && $stable(sel) && $fell(in0)) |-> $fell(out)
    );

    // With sel=1 stable, a rising edge on in1 causes a rising edge on out.
    track_rise_sel1: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel==1'b1 && $stable(sel) && $rose(in1)) |-> $rose(out)
    );

    // With sel=1 stable, a falling edge on in1 causes a falling edge on out.
    track_fall_sel1: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel==1'b1 && $stable(sel) && $fell(in1)) |-> $fell(out)
    );

    // If inputs are equal and sel changes, out does not change.
    equal_inputs_sel_change_no_effect: assert property (
        @(posedge CLK) disable iff (!RESETn) (in0==in1 && $changed(sel)) |-> $stable(out)
    );
endmodule