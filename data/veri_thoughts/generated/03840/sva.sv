module my_flipflop_sva (
    input logic in,
    input logic clock,
    input logic enable_l,
    input logic reset,
    input logic clear,
    input logic out,
    input logic q1,
    input logic q2,
    input logic q3,
    input logic q4
);

    // q1 loads input on an enabled clock.
    check_shift_q1: assert property (
        @(posedge clock) disable iff (reset)
        (enable_l == 1'b0) |=> (q1 == $past(in))
    );

    // q2 loads the previous q1 on an enabled clock.
    check_shift_q2: assert property (
        @(posedge clock) disable iff (reset)
        (enable_l == 1'b0) |=> (q2 == $past(q1))
    );

    // q3 loads the previous q2 on an enabled clock.
    check_shift_q3: assert property (
        @(posedge clock) disable iff (reset)
        (enable_l == 1'b0) |=> (q3 == $past(q2))
    );

    // q4 loads the previous q3 on an enabled clock.
    check_shift_q4: assert property (
        @(posedge clock) disable iff (reset)
        (enable_l == 1'b0) |=> (q4 == $past(q3))
    );

    // The shift registers hold when the active-low enable is deasserted.
    check_hold_when_disabled: assert property (
        @(posedge clock) disable iff (reset)
        (enable_l == 1'b1) |=> (
            q1 == $past(q1) &&
            q2 == $past(q2) &&
            q3 == $past(q3) &&
            q4 == $past(q4)
        )
    );

    // Reset forces out low.
    check_reset_forces_out_low: assert property (
        @(posedge clock)
        (reset == 1'b1) |-> (out == 1'b0)
    );

    // Clear forces out high when reset is not asserted.
    check_clear_forces_out_high: assert property (
        @(posedge clock) disable iff (reset)
        (clear == 1'b1) |-> (out == 1'b1)
    );

    // The 1010 q-pattern forces out low.
    check_pattern_1010_forces_out_low: assert property (
        @(posedge clock) disable iff (reset)
        (clear == 1'b0 &&
         q4 == 1'b1 &&
         q3 == 1'b0 &&
         q2 == 1'b1 &&
         q1 == 1'b0) |-> (out == 1'b0)
    );

    // The 0101 q-pattern forces out high.
    check_pattern_0101_forces_out_high: assert property (
        @(posedge clock) disable iff (reset)
        (clear == 1'b0 &&
         q4 == 1'b0 &&
         q3 == 1'b1 &&
         q2 == 1'b0 &&
         q1 == 1'b1) |-> (out == 1'b1)
    );

    // Outside reset, clear, and special patterns, out follows q4.
    check_default_out_follows_q4: assert property (
        @(posedge clock) disable iff (reset)
        (clear == 1'b0 &&
         !(q4 == 1'b1 && q3 == 1'b0 && q2 == 1'b1 && q1 == 1'b0) &&
         !(q4 == 1'b0 && q3 == 1'b1 && q2 == 1'b0 && q1 == 1'b1)) |-> (out == q4)
    );

endmodule