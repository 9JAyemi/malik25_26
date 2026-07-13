module blinker_sva (
    input logic clk,
    input logic rst,
    input logic blink,
    input logic [24:0] counter_q,
    input logic [24:0] counter_d,
    input logic dir
);
    // Clock: clk; Reset: rst (active-high, synchronous). Mixed: sequential (counter_q, dir) + combinational (counter_d, blink).

    ///// Reset behavior /////
    // On reset, next cycle counter_q and dir are 0.
    reset_clears_regs_next: assert property (
        @(posedge clk) rst |=> (counter_q == 25'b0) && (dir == 1'b0)
    );
    // While reset is held, regs remain 0.
    hold_zero_while_reset: assert property (
        @(posedge clk) ($past(rst) && rst) |-> (counter_q == 25'b0) && (dir == 1'b0)
    );
    // After a reset cycle, blink is 0 on the next cycle.
    blink_zero_after_reset: assert property (
        @(posedge clk) rst |=> (blink == 1'b0)
    );

    ///// Combinational next-state logic /////
    // When dir==0, next-state increments by 1.
    counterd_inc_when_dir0: assert property (
        @(posedge clk) disable iff (rst) (!dir) |-> (counter_d == counter_q + 25'd1)
    );
    // When dir==1, next-state decrements by 1.
    counterd_dec_when_dir1: assert property (
        @(posedge clk) disable iff (rst) (dir) |-> (counter_d == counter_q - 25'd1)
    );
    // LSB of next-state always toggles relative to current state (±1 operation).
    lsb_toggles_between_q_and_d: assert property (
        @(posedge clk) disable iff (rst) (counter_d[0] == ~counter_q[0])
    );

    ///// Sequential update /////
    // When not in reset, counter_q loads prior counter_d on the next cycle.
    q_follows_d_next: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (counter_q == $past(counter_d))
    );
    // When not in reset, dir holds its value (no updates outside reset).
    dir_stable_without_reset: assert property (
        @(posedge clk) disable iff (rst) (!rst && $past(!rst)) |-> (dir == $past(dir))
    );
    // Counter_q steps by ±1 each cycle according to dir.
    counterq_steps_by_one: assert property (
        @(posedge clk) disable iff (rst)
            1'b1 |=> (counter_q == ($past(dir) ? ($past(counter_q) - 25'd1) : ($past(counter_q) + 25'd1)))
    );

    ///// Output mapping /////
    // blink mirrors the MSB of counter_d.
    blink_matches_counterd_msb: assert property (
        @(posedge clk) (blink == counter_d[24])
    );
    // When not in reset, blink equals MSB of (dir ? (q-1) : (q+1)).
    blink_function_of_q_and_dir: assert property (
        @(posedge clk) disable iff (rst)
            (blink == (dir ? (counter_q - 25'd1)[24] : (counter_q + 25'd1)[24]))
    );

endmodule