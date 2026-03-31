module udp_mux_4to1_sva (
    input logic clk,
    input logic [3:0] out,
    input logic [3:0] in0, in1, in2, in3,
    input logic [1:0] sel
);
    ///// Bit[1]/[2]/[3] select behavior on sel[0] edges /////
    // When sel[0] rises, out[1] takes in1[1].
    out1_follows_in1_on_sel0_rise: assert property (
        @(posedge clk) disable iff (1'b0) $rose(sel[0]) |-> (out[1] == in1[1])
    );
    // When sel[0] falls, out[1] takes in0[1].
    out1_follows_in0_on_sel0_fall: assert property (
        @(posedge clk) disable iff (1'b0) $fell(sel[0]) |-> (out[1] == in0[1])
    );
    // When sel[0] rises, out[2] takes in3[2].
    out2_follows_in3_on_sel0_rise: assert property (
        @(posedge clk) disable iff (1'b0) $rose(sel[0]) |-> (out[2] == in3[2])
    );
    // When sel[0] falls, out[2] takes in2[2].
    out2_follows_in2_on_sel0_fall: assert property (
        @(posedge clk) disable iff (1'b0) $fell(sel[0]) |-> (out[2] == in2[2])
    );
    // When sel[0] rises, out[3] takes in1[3].
    out3_follows_in1_on_sel0_rise: assert property (
        @(posedge clk) disable iff (1'b0) $rose(sel[0]) |-> (out[3] == in1[3])
    );
    // When sel[0] falls, out[3] takes in0[3].
    out3_follows_in0_on_sel0_fall: assert property (
        @(posedge clk) disable iff (1'b0) $fell(sel[0]) |-> (out[3] == in0[3])
    );

    ///// Output change gating /////
    // out[0] can only change when sel[1] changes.
    out0_changes_only_with_sel1: assert property (
        @(posedge clk) disable iff (1'b0) $changed(out[0]) |-> $changed(sel[1])
    );
    // out[1] can only change when sel[0] changes.
    out1_changes_only_with_sel0: assert property (
        @(posedge clk) disable iff (1'b0) $changed(out[1]) |-> $changed(sel[0])
    );
    // out[2] can only change when sel[0] changes.
    out2_changes_only_with_sel0: assert property (
        @(posedge clk) disable iff (1'b0) $changed(out[2]) |-> $changed(sel[0])
    );
    // out[3] can only change when sel[0] changes.
    out3_changes_only_with_sel0: assert property (
        @(posedge clk) disable iff (1'b0) $changed(out[3]) |-> $changed(sel[0])
    );

    ///// Stability when unrelated select is stable /////
    // If sel[1] is stable, out[0] is stable.
    out0_stable_when_sel1_stable: assert property (
        @(posedge clk) disable iff (1'b0) $stable(sel[1]) |-> $stable(out[0])
    );
    // If sel[0] is stable, out[1], out[2], out[3] are stable.
    out123_stable_when_sel0_stable: assert property (
        @(posedge clk) disable iff (1'b0) $stable(sel[0]) |-> ($stable(out[1]) && $stable(out[2]) && $stable(out[3]))
    );

    ///// Independence of other select /////
    // Changing sel[0] alone does not affect out[0].
    out0_ignores_sel0_when_sel1_stable: assert property (
        @(posedge clk) disable iff (1'b0) $changed(sel[0]) && $stable(sel[1]) |-> $stable(out[0])
    );
    // Changing sel[1] alone does not affect out[1..3].
    out123_ignores_sel1_when_sel0_stable: assert property (
        @(posedge clk) disable iff (1'b0) $changed(sel[1]) && $stable(sel[0]) |-> ($stable(out[1]) && $stable(out[2]) && $stable(out[3]))
    );
endmodule