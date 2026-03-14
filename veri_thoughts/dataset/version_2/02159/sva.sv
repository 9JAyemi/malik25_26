module mux_2to1_pipeline_sva (
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic out_always,
    input logic clk,
    input logic pipeline_reg
);
    // pipeline_reg captures sel_b1 with one-cycle latency.
    pipe_tracks_sel_b1: assert property (
        @(posedge clk) disable iff ($initstate) pipeline_reg == $past(sel_b1)
    );

    // A rising pipeline_reg means sel_b1 was 1 in the previous cycle.
    pipe_rise_matches_prev_sel1: assert property (
        @(posedge clk) disable iff ($initstate) $rose(pipeline_reg) |-> $past(sel_b1)
    );

    // A falling pipeline_reg means sel_b1 was 0 in the previous cycle.
    pipe_fall_matches_prev_sel0: assert property (
        @(posedge clk) disable iff ($initstate) $fell(pipeline_reg) |-> !$past(sel_b1)
    );

    // out_always equals the mux of a/b selected by pipeline_reg.
    out_matches_selected_input: assert property (
        @(posedge clk) disable iff ($initstate) out_always == (pipeline_reg ? b : a)
    );

    // When selecting a and both a and select are stable, out_always is stable.
    out_stable_when_a_selected_and_stable: assert property (
        @(posedge clk) disable iff ($initstate)
            (pipeline_reg == 1'b0 && $stable(a) && $stable(pipeline_reg)) |-> $stable(out_always)
    );

    // When selecting b and both b and select are stable, out_always is stable.
    out_stable_when_b_selected_and_stable: assert property (
        @(posedge clk) disable iff ($initstate)
            (pipeline_reg == 1'b1 && $stable(b) && $stable(pipeline_reg)) |-> $stable(out_always)
    );

    // An out_always change must be caused by a change in the select or the selected input.
    out_change_has_cause: assert property (
        @(posedge clk) disable iff ($initstate)
            $changed(out_always) |-> ($changed(pipeline_reg) || (pipeline_reg ? $changed(b) : $changed(a)))
    );
endmodule