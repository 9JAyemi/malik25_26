module shift_register_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // q reflects the previous cycle's d value.
    check_q_captures_d: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(d))
    );

    // The first cycle after a 1 on d is reflected on q.
    check_q_high_after_d_high: assert property (
        @(posedge clk) d |=> q
    );

    // The first cycle after a 0 on d is reflected on q.
    check_q_low_after_d_low: assert property (
        @(posedge clk) !d |=> !q
    );

    // A high q must come from a high d on the previous cycle.
    check_q_high_has_high_d_cause: assert property (
        @(posedge clk) q |-> $past(d)
    );

    // A low q must come from a low d on the previous cycle.
    check_q_low_has_low_d_cause: assert property (
        @(posedge clk) !q |-> !$past(d)
    );

endmodule