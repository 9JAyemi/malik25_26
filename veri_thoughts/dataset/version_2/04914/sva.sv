module dff_sr_clr_sva (
    input logic clk,
    input logic d,
    input logic set,
    input logic reset,
    input logic clr,
    input logic q,
    input logic qn
);

    // Clock: clk
    // Synchronous controls: clr is active-low, reset is active-high, set is active-high
    // q is sequential and qn is combinational

    // Low clear has highest priority and drives q low.
    check_clear_priority_drives_q_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (clr == 1'b0) |=> (q == 1'b0)
    );

    // High reset drives q low when clear is inactive.
    check_reset_drives_q_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (clr == 1'b1 && reset == 1'b1) |=> (q == 1'b0)
    );

    // High set drives q high when clear and reset are inactive.
    check_set_drives_q_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (clr == 1'b1 && reset == 1'b0 && set == 1'b1) |=> (q == 1'b1)
    );

    // d is captured when clear, reset, and set are inactive.
    check_d_captured_when_controls_inactive: assert property (
        @(posedge clk) disable iff (1'b0)
        (clr == 1'b1 && reset == 1'b0 && set == 1'b0) |=> (q == $past(d))
    );

    // q matches the previous cycle's prioritized input selection.
    check_q_matches_prioritized_next_state: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (
            q == (
                ($past(clr) == 1'b0) ? 1'b0 :
                ($past(reset) == 1'b1) ? 1'b0 :
                ($past(set) == 1'b1) ? 1'b1 :
                                       $past(d)
            )
        )
    );

    // qn is always the inverse of q.
    check_qn_is_inverse_of_q: assert property (
        @(posedge clk) disable iff (1'b0)
        (qn == ~q)
    );

endmodule