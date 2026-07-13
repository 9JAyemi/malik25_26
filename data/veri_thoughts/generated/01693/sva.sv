module d_ff_sr_sva (
    input logic clk,
    input logic rst,   // active-low async reset
    input logic set,
    input logic d,
    input logic q
);

    ///// Reset behavior /////
    // When reset is asserted (low), q must be 0 at the sample.
    check_reset_forces_q0_now: assert property (
        @(posedge clk) !rst |-> (q == 1'b0)
    );

    // If reset was low on the previous cycle, q is 0 now.
    check_prev_reset_keeps_q0: assert property (
        @(posedge clk) $past(!rst) |-> (q == 1'b0)
    );

    ///// Functional behavior (gated off during reset) /////
    // With reset deasserted, set=1 drives q to 1 on the next clock.
    check_set_drives_one_next: assert property (
        @(posedge clk) disable iff (!rst) set |=> (!rst || (q == 1'b1))
    );

    // With reset deasserted and set=0, q captures d on the next clock.
    check_no_set_captures_d_next: assert property (
        @(posedge clk) disable iff (!rst) !set |=> (!rst || (q == $past(d)))
    );

    // Set has priority over data when d=0 (q still becomes 1 next).
    check_set_overrides_data_when_d0: assert property (
        @(posedge clk) disable iff (!rst) (set && (d == 1'b0)) |=> (!rst || (q == 1'b1))
    );

    // When set=0 and d=0, q becomes 0 on the next clock.
    check_no_set_d0_yields_q0: assert property (
        @(posedge clk) disable iff (!rst) (!set && (d == 1'b0)) |=> (!rst || (q == 1'b0))
    );

    // When set=0 and d=1, q becomes 1 on the next clock.
    check_no_set_d1_yields_q1: assert property (
        @(posedge clk) disable iff (!rst) (!set && (d == 1'b1)) |=> (!rst || (q == 1'b1))
    );

    // If set=0 and previous d equals previous q, q holds its value.
    check_hold_when_no_set_and_prev_d_eq_prev_q: assert property (
        @(posedge clk) disable iff (!rst) (!set && ($past(d) == $past(q))) |=> (!rst || (q == $past(q)))
    );

endmodule