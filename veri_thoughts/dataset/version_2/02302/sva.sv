module MUX4_sva (
    input logic clk,        // sampling clock for assertions (DUT is combinational, no reset)
    input logic a0,
    input logic a1,
    input logic b0,
    input logic b1,
    input logic sel0,
    input logic sel1,
    input logic out
);
    // out equals the functional composition of the three MUX2 instances
    check_mux4_functional_equiv: assert property (
        @(posedge clk) out == (sel1 ? (sel0 ? b1 : b0) : (sel0 ? a1 : a0))
    );

    // When sel1=0 and sel0=0 then out=a0
    check_mux4_path_sel00: assert property (
        @(posedge clk) (!sel1 && !sel0) |-> (out == a0)
    );

    // When sel1=0 and sel0=1 then out=a1
    check_mux4_path_sel01: assert property (
        @(posedge clk) (!sel1 && sel0) |-> (out == a1)
    );

    // When sel1=1 and sel0=0 then out=b0
    check_mux4_path_sel10: assert property (
        @(posedge clk) (sel1 && !sel0) |-> (out == b0)
    );

    // When sel1=1 and sel0=1 then out=b1
    check_mux4_path_sel11: assert property (
        @(posedge clk) (sel1 && sel0) |-> (out == b1)
    );

    // If sel1=0 and a0==a1 then out equals that common value
    check_mux4_agroup_uniform: assert property (
        @(posedge clk) (!sel1 && (a0 == a1)) |-> (out == a0)
    );

    // If sel1=1 and b0==b1 then out equals that common value
    check_mux4_bgroup_uniform: assert property (
        @(posedge clk) (sel1 && (b0 == b1)) |-> (out == b0)
    );

    // Rising sel0 under sel1=0 transitions out from a0 (prev) to a1 (now)
    check_out_tracks_sel0_rise_when_sel1_0: assert property (
        @(posedge clk) $rose(sel0) && (sel1 == 1'b0) && ($past(sel1) == 1'b0)
        |-> (out == a1) && ($past(out) == $past(a0))
    );

    // Falling sel0 under sel1=0 transitions out from a1 (prev) to a0 (now)
    check_out_tracks_sel0_fall_when_sel1_0: assert property (
        @(posedge clk) $fell(sel0) && (sel1 == 1'b0) && ($past(sel1) == 1'b0)
        |-> (out == a0) && ($past(out) == $past(a1))
    );

    // Rising sel1 switches source from a-group (prev) to b-group (now)
    check_out_tracks_sel1_rise: assert property (
        @(posedge clk) $rose(sel1)
        |-> (out == (sel0 ? b1 : b0)) && ($past(out) == ($past(sel0) ? $past(a1) : $past(a0)))
    );

    // Falling sel1 switches source from b-group (prev) to a-group (now)
    check_out_tracks_sel1_fall: assert property (
        @(posedge clk) $fell(sel1)
        |-> (out == (sel0 ? a1 : a0)) && ($past(out) == ($past(sel0) ? $past(b1) : $past(b0)))
    );

    // When sel1=0, changes on unselected b-inputs do not affect out if selected path is stable
    check_unselected_b_noeffect_when_sel1_0: assert property (
        @(posedge clk) (sel1 == 1'b0) && $stable(sel1) && $stable(sel0) && $stable(a0) && $stable(a1) && ($changed(b0) || $changed(b1))
        |-> $stable(out)
    );

    // When sel1=1, changes on unselected a-inputs do not affect out if selected path is stable
    check_unselected_a_noeffect_when_sel1_1: assert property (
        @(posedge clk) (sel1 == 1'b1) && $stable(sel1) && $stable(sel0) && $stable(b0) && $stable(b1) && ($changed(a0) || $changed(a1))
        |-> $stable(out)
    );
endmodule