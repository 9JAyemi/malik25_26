module count3_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic out,
    input logic [1:0] cnt
);
    // out reflects cnt==3 exactly.
    check_out_matches_cnt: assert property (
        @(posedge clk) disable iff (reset) out == (cnt == 2'd3)
    );

    // When enabled and not at 3, cnt increments by 1 on the next cycle.
    check_inc_on_enable: assert property (
        @(posedge clk) disable iff (reset) (enable && (cnt != 2'd3)) |=> (cnt == $past(cnt) + 2'd1)
    );

    // When cnt==3, it clears to 0 on the next cycle.
    check_clear_after_3: assert property (
        @(posedge clk) disable iff (reset) (cnt == 2'd3) |=> (cnt == 2'd0)
    );

    // When disabled, cnt clears to 0 on the next cycle.
    check_clear_on_disable: assert property (
        @(posedge clk) disable iff (reset) (!enable) |=> (cnt == 2'd0)
    );

    // out pulses are single-cycle.
    check_out_single_cycle: assert property (
        @(posedge clk) disable iff (reset) out |=> !out
    );

    // There are at least three low cycles of out between pulses.
    check_out_min_gap_3: assert property (
        @(posedge clk) disable iff (reset) out |=> !out[*3]
    );

    // A rising out implies previous cnt==2 and enable was 1.
    check_out_rise_preconds: assert property (
        @(posedge clk) disable iff (reset) $rose(out) |-> ($past(cnt) == 2'd2) && $past(enable)
    );

    // If cnt==2 and enabled, out is high in the next cycle.
    check_cnt2_enable_leads_out: assert property (
        @(posedge clk) disable iff (reset) (enable && (cnt == 2'd2)) |=> out
    );

    // If cnt==0 or 1 and enabled, out is low in the next cycle.
    check_cnt01_enable_no_out_next: assert property (
        @(posedge clk) disable iff (reset) (enable && ((cnt == 2'd0) || (cnt == 2'd1))) |=> !out
    );
endmodule