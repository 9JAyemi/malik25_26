module wait_time_module_sva (
    input logic clk,
    input logic reset,       // active-low reset in RTL
    input logic work,
    input logic [11:0] wait_time,
    input logic [5:0] i      // internal counter from RTL
);
    ///// Reset behavior /////
    // During reset, wait_time and i must be zero.
    reset_forces_regs_zero: assert property (
        @(posedge clk) !reset |-> (wait_time == 12'd0) && (i == 6'd0)
    );

    ///// Counter i behavior /////
    // i never exceeds 4 when not in reset.
    i_within_0_to_4: assert property (
        @(posedge clk) disable iff (!reset) (i <= 6'd4)
    );
    // When work is 0, i clears to 0 on the next cycle.
    clear_i_on_work0_next: assert property (
        @(posedge clk) disable iff (!reset) (work == 1'b0) |=> (i == 6'd0)
    );
    // With work=1 and i<4, i increments by 1 on the next cycle.
    inc_i_when_work1_lt4: assert property (
        @(posedge clk) disable iff (!reset) (work && (i < 6'd4)) |=> (i == $past(i) + 6'd1)
    );
    // With work=1 and i>=4, i clears to 0 on the next cycle.
    clear_i_when_work1_ge4: assert property (
        @(posedge clk) disable iff (!reset) (work && (i >= 6'd4)) |=> (i == 6'd0)
    );
    // i==4 must come from i==3 with work=1 in the previous cycle.
    i4_from_i3_with_work1: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && (i == 6'd4)) |-> ($past(i) == 6'd3 && $past(work) == 1'b1)
    );

    ///// wait_time behavior /////
    // When no increment trigger (not work && i>=4), wait_time holds next cycle.
    hold_wait_when_not_triggered: assert property (
        @(posedge clk) disable iff (!reset) (!(work && (i >= 6'd4))) |=> (wait_time == $past(wait_time))
    );
    // Any wait_time change must be caused by prior work=1 and i>=4.
    wait_change_requires_trigger: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && (wait_time != $past(wait_time))) |-> ($past(work) && ($past(i) >= 6'd4))
    );
    // On prior work=1 and i>=4, wait_time increments by exactly 1 with wrap.
    inc_wait_magnitude_on_trigger: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset) && $past(work) && ($past(i) >= 6'd4))
            |-> (
                (($past(wait_time) == 12'hFFF) && (wait_time == 12'h000)) ||
                (($past(wait_time) != 12'hFFF) && (wait_time == $past(wait_time) + 12'd1))
            )
    );
    // If work was 0 in the previous cycle, wait_time holds this cycle.
    hold_wait_after_work0: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && ($past(work) == 1'b0)) |-> (wait_time == $past(wait_time))
    );
endmodule