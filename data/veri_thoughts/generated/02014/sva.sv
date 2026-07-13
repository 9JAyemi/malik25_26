module up_down_counter_sva (
    input logic clk,
    input logic n_rst,
    input logic up,
    input logic dn,
    input logic [3:0] cnt,
    input logic out1,
    input logic out2
);
    // Clock: clk; Reset: n_rst (active-low, asynchronous)
    // Logic: mixed (seq cnt register with async reset; comb next-state and outputs)
    // Behavior: 4-bit saturating up/down counter; hold when both or none; out2=cnt[0], out1=~cnt[0]

    // During active reset, counter is 0 and outputs reflect LSB
    check_reset_state: assert property (
        @(posedge clk) !n_rst |-> (cnt == 4'd0) && (out2 == 1'b0) && (out1 == 1'b1)
    );

    // out2 always equals cnt LSB
    check_out2_matches_cnt_lsb: assert property (
        @(posedge clk) disable iff (!n_rst) out2 == cnt[0]
    );

    // out1 always equals complement of cnt LSB
    check_out1_complements_cnt_lsb: assert property (
        @(posedge clk) disable iff (!n_rst) out1 == ~cnt[0]
    );

    // Increment by 1 when up=1, dn=0, and not at max (based on previous cycle)
    check_increment_when_up_only: assert property (
        @(posedge clk) disable iff (!n_rst)
            $past(n_rst && up && !dn && (cnt < 4'hf)) |-> (cnt == $past(cnt) + 4'd1)
    );

    // Hold at max when up=1, dn=0, and at 0xF (saturate high)
    check_saturate_at_max_on_up: assert property (
        @(posedge clk) disable iff (!n_rst)
            $past(n_rst && up && !dn && (cnt == 4'hf)) |-> (cnt == 4'hf)
    );

    // Decrement by 1 when dn=1, up=0, and not at zero (based on previous cycle)
    check_decrement_when_dn_only: assert property (
        @(posedge clk) disable iff (!n_rst)
            $past(n_rst && dn && !up && (cnt > 4'd0)) |-> (cnt == $past(cnt) - 4'd1)
    );

    // Hold at zero when dn=1, up=0, and at 0 (saturate low)
    check_saturate_at_zero_on_dn: assert property (
        @(posedge clk) disable iff (!n_rst)
            $past(n_rst && dn && !up && (cnt == 4'd0)) |-> (cnt == 4'd0)
    );

    // Hold when both controls are deasserted
    check_hold_when_both_low: assert property (
        @(posedge clk) disable iff (!n_rst)
            $past(n_rst && !up && !dn) |-> (cnt == $past(cnt))
    );

    // Hold when both controls are asserted
    check_hold_when_both_high: assert property (
        @(posedge clk) disable iff (!n_rst)
            $past(n_rst && up && dn) |-> (cnt == $past(cnt))
    );

    // From mid-range (1..14), next value changes by at most 1 or holds
    check_unit_step_in_midrange: assert property (
        @(posedge clk) disable iff (!n_rst)
            $past(n_rst && (cnt > 4'd0) && (cnt < 4'hf)) |->
                ( (cnt == $past(cnt)) ||
                  (cnt == $past(cnt) + 4'd1) ||
                  (cnt == $past(cnt) - 4'd1) )
    );

endmodule