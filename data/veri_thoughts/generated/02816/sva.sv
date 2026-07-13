module mux_2to1_sva (
    input logic out,
    input logic in0,
    input logic in1,
    input logic sel
);
    // No clock/reset in RTL; pure combinational mux: out=in0 when sel==0 else out=in1 (including sel=X/Z).

    // When sel is exactly 0, out must equal in0.
    check_out_when_sel0: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1 or posedge sel or negedge sel)
        (sel === 1'b0) |-> (out === in0)
    );

    // When sel is exactly 1, out must equal in1.
    check_out_when_sel1: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1 or posedge sel or negedge sel)
        (sel === 1'b1) |-> (out === in1)
    );

    // When sel is X/Z (not 0 and not 1), out must equal in1 per the else branch.
    check_out_when_selx: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1 or posedge sel or negedge sel)
        ((sel !== 1'b0) && (sel !== 1'b1)) |-> (out === in1)
    );

    // Out must always equal one of the two inputs.
    check_out_is_one_of_inputs: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1 or posedge sel or negedge sel)
        ( (out === in0) || (out === in1) )
    );

    // With sel==0, any out change (not due to sel change) must be caused by in0 changing.
    check_out_change_caused_by_in0_when_sel0: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1 or posedge sel or negedge sel)
        (sel === 1'b0 && !$changed(sel) && $changed(out)) |-> $changed(in0)
    );

    // With sel==1, any out change (not due to sel change) must be caused by in1 changing.
    check_out_change_caused_by_in1_when_sel1: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1 or posedge sel or negedge sel)
        (sel === 1'b1 && !$changed(sel) && $changed(out)) |-> $changed(in1)
    );

    // With sel==X/Z, any out change (not due to sel change) must be caused by in1 changing.
    check_out_change_caused_by_in1_when_selx: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1 or posedge sel or negedge sel)
        ((sel !== 1'b0 && sel !== 1'b1) && !$changed(sel) && $changed(out)) |-> $changed(in1)
    );

    // With sel==0 and in0/sel stable, out must remain stable (in1 changes cannot affect out).
    check_stable_out_when_sel0_and_in0_sel_stable: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1 or posedge sel or negedge sel)
        (sel === 1'b0 && !$changed(in0) && !$changed(sel)) |-> !$changed(out)
    );

    // With sel==1 and in1/sel stable, out must remain stable (in0 changes cannot affect out).
    check_stable_out_when_sel1_and_in1_sel_stable: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1 or posedge sel or negedge sel)
        (sel === 1'b1 && !$changed(in1) && !$changed(sel)) |-> !$changed(out)
    );

    // With sel==X/Z and in1/sel stable, out must remain stable.
    check_stable_out_when_selx_and_in1_sel_stable: assert property (
        @(posedge in0 or negedge in0 or posedge in1 or negedge in1 or posedge sel or negedge sel)
        ((sel !== 1'b0 && sel !== 1'b1) && !$changed(in1) && !$changed(sel)) |-> !$changed(out)
    );

    // Toggling sel does not change out when in0==in1 and inputs are stable since the last sel edge.
    check_no_glitch_on_sel_toggle_when_inputs_equal: assert property (
        @(posedge sel or negedge sel)
        ((in0 === in1) && !$changed(in0) && !$changed(in1)) |-> !$changed(out)
    );

endmodule