module AND4X_sva (
    input logic IN1,
    input logic IN2,
    input logic IN3,
    input logic IN4,
    input logic Q
);

    // Q matches the 4-input AND of the inputs.
    check_q_matches_and4: assert property (
        @($global_clock) Q == (IN1 & IN2 & IN3 & IN4)
    );

    // Q is high when all inputs are high.
    check_q_high_when_all_inputs_high: assert property (
        @($global_clock) (IN1 & IN2 & IN3 & IN4) |-> Q
    );

    // IN1 low forces Q low.
    check_q_low_when_in1_low: assert property (
        @($global_clock) !IN1 |-> !Q
    );

    // IN2 low forces Q low.
    check_q_low_when_in2_low: assert property (
        @($global_clock) !IN2 |-> !Q
    );

    // IN3 low forces Q low.
    check_q_low_when_in3_low: assert property (
        @($global_clock) !IN3 |-> !Q
    );

    // IN4 low forces Q low.
    check_q_low_when_in4_low: assert property (
        @($global_clock) !IN4 |-> !Q
    );

    // Q high implies IN1 is high.
    check_q_implies_in1_high: assert property (
        @($global_clock) Q |-> IN1
    );

    // Q high implies IN2 is high.
    check_q_implies_in2_high: assert property (
        @($global_clock) Q |-> IN2
    );

    // Q high implies IN3 is high.
    check_q_implies_in3_high: assert property (
        @($global_clock) Q |-> IN3
    );

    // Q high implies IN4 is high.
    check_q_implies_in4_high: assert property (
        @($global_clock) Q |-> IN4
    );

endmodule