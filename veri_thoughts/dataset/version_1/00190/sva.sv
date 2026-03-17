module small_fifo_cntr_sva (
    input logic       aclr,
    input logic       clock,
    input logic       cnt_en,
    input logic       updown,
    input logic [2:0] q,
    input logic       sclr
);

    // Sampled async clear forces q low by the next clock.
    check_aclr_clears_q: assert property (
        @(posedge clock)
        aclr |=> (q == 3'b000)
    );

    // Sync clear forces q low on the following cycle.
    check_sclr_clears_q: assert property (
        @(posedge clock) disable iff (aclr)
        sclr |=> (q == 3'b000)
    );

    // Sync clear overrides an enabled count.
    check_sclr_priority_over_count: assert property (
        @(posedge clock) disable iff (aclr)
        sclr && cnt_en |=> (q == 3'b000)
    );

    // q increments by one when enabled to count up.
    check_count_up: assert property (
        @(posedge clock) disable iff (aclr)
        !sclr && cnt_en && updown |=> (q == ($past(q) + 3'b001))
    );

    // q decrements by one when enabled to count down.
    check_count_down: assert property (
        @(posedge clock) disable iff (aclr)
        !sclr && cnt_en && !updown |=> (q == ($past(q) - 3'b001))
    );

    // q holds its value when no clear or count is requested.
    check_hold_when_disabled: assert property (
        @(posedge clock) disable iff (aclr)
        !sclr && !cnt_en |=> (q == $past(q))
    );

endmodule