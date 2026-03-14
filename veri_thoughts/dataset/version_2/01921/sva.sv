module PushButton_Debouncer_sva (
    input logic clk,
    input logic PB,
    input logic PB_state,
    input logic PB_down,
    input logic PB_up,
    // Internal signals from RTL (bind hierarchically)
    input logic PB_sync_0,
    input logic PB_sync_1,
    input logic [15:0] PB_cnt,
    input logic PB_idle,
    input logic PB_cnt_max
);
    // PB_sync_0 samples inverted PB (1-cycle delayed in assertion sampling)
    check_sync0_tracks_PB: assert property (
        @(posedge clk) disable iff ($initstate) PB_sync_0 == $past(~PB)
    );

    // PB_sync_1 follows PB_sync_0 by 1 cycle
    check_sync1_tracks_sync0: assert property (
        @(posedge clk) disable iff ($initstate) PB_sync_1 == $past(PB_sync_0)
    );

    // PB_idle is exactly (PB_state == PB_sync_1)
    check_idle_definition: assert property (
        @(posedge clk) disable iff ($initstate) PB_idle == (PB_state == PB_sync_1)
    );

    // PB_cnt_max is the AND-reduction of PB_cnt
    check_cntmax_definition: assert property (
        @(posedge clk) disable iff ($initstate) PB_cnt_max == (&PB_cnt)
    );

    // If idle last cycle, counter is 0 now
    check_cnt_resets_when_idle_prev: assert property (
        @(posedge clk) disable iff ($initstate) $past(PB_idle) |-> (PB_cnt == 16'd0)
    );

    // If active last cycle, counter increments by 1 now (with wrap)
    check_cnt_increments_when_active_prev: assert property (
        @(posedge clk) disable iff ($initstate) $past(!PB_idle) |-> (PB_cnt == $past(PB_cnt) + 16'd1)
    );

    // PB_state only changes when active and counter was max last cycle
    check_state_changes_only_on_max: assert property (
        @(posedge clk) disable iff ($initstate) $changed(PB_state) |-> $past(!PB_idle & PB_cnt_max)
    );

    // When active and counter was max last cycle, PB_state toggles
    check_state_changes_when_required: assert property (
        @(posedge clk) disable iff ($initstate) $past(!PB_idle & PB_cnt_max) |-> (PB_state == ~$past(PB_state))
    );

    // PB_down is exactly asserted when not idle, cnt max, and state low
    check_pb_down_definition: assert property (
        @(posedge clk) disable iff ($initstate) PB_down == (~PB_idle & PB_cnt_max & ~PB_state)
    );

    // PB_up is exactly asserted when not idle, cnt max, and state high
    check_pb_up_definition: assert property (
        @(posedge clk) disable iff ($initstate) PB_up == (~PB_idle & PB_cnt_max & PB_state)
    );

    // PB_down implies PB_up is LOW in the same cycle
    check_down_implies_not_up: assert property (
        @(posedge clk) disable iff ($initstate) PB_down |-> !PB_up
    );

    // PB_up implies PB_down is LOW in the same cycle
    check_up_implies_not_down: assert property (
        @(posedge clk) disable iff ($initstate) PB_up |-> !PB_down
    );

    // PB_down is a single-cycle pulse
    check_pb_down_single_cycle: assert property (
        @(posedge clk) disable iff ($initstate) PB_down |-> ##1 !PB_down
    );

    // PB_up is a single-cycle pulse
    check_pb_up_single_cycle: assert property (
        @(posedge clk) disable iff ($initstate) PB_up |-> ##1 !PB_up
    );
endmodule