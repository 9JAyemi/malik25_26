module lfsr_3bit_sva (
    input logic CLK,
    input logic Q0,
    input logic Q1,
    input logic Q2
);

    // Q2 shifts in the previous Q1 value.
    check_q2_shift: assert property (
        @(posedge CLK) 1'b1 |=> (Q2 == $past(Q1))
    );

    // Q1 shifts in the previous Q0 value.
    check_q1_shift: assert property (
        @(posedge CLK) 1'b1 |=> (Q1 == $past(Q0))
    );

    // Q0 is the XOR of the previous Q2 and Q1 values.
    check_q0_feedback: assert property (
        @(posedge CLK) 1'b1 |=> (Q0 == ($past(Q2) ^ $past(Q1)))
    );

    // The full 3-bit output state follows the RTL next-state function.
    check_state_update: assert property (
        @(posedge CLK) 1'b1 |=> ({Q2, Q1, Q0} == {$past(Q1), $past(Q0), ($past(Q2) ^ $past(Q1))})
    );

    // Equal previous Q2 and Q1 drive Q0 low on the next cycle.
    check_feedback_zero_case: assert property (
        @(posedge CLK) (Q2 == Q1) |=> (Q0 == 1'b0)
    );

    // Different previous Q2 and Q1 drive Q0 high on the next cycle.
    check_feedback_one_case: assert property (
        @(posedge CLK) (Q2 != Q1) |=> (Q0 == 1'b1)
    );

    // The all-zero state remains all-zero on the next cycle.
    check_zero_lockup: assert property (
        @(posedge CLK) ({Q2, Q1, Q0} == 3'b000) |=> ({Q2, Q1, Q0} == 3'b000)
    );

endmodule