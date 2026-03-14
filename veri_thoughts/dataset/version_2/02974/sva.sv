module logic_module_sva (
    input logic IN1,
    input logic IN2,
    input logic IN3,
    input logic Q
);
    // Q must equal IN1 & IN2 & ~IN3 at sampling points.
    check_q_definition: assert property (
        @(posedge IN1 or posedge IN2 or posedge IN3 or posedge Q) Q == (IN1 & IN2 & ~IN3)
    );

    // If IN3 is HIGH, Q must be LOW.
    check_q_zero_when_in3_high: assert property (
        @(posedge IN1 or posedge IN2 or posedge IN3 or posedge Q) IN3 |-> (Q == 1'b0)
    );

    // If IN1 is LOW, Q must be LOW.
    check_q_zero_when_in1_low: assert property (
        @(posedge IN1 or posedge IN2 or posedge IN3 or posedge Q) !IN1 |-> (Q == 1'b0)
    );

    // If IN2 is LOW, Q must be LOW.
    check_q_zero_when_in2_low: assert property (
        @(posedge IN1 or posedge IN2 or posedge IN3 or posedge Q) !IN2 |-> (Q == 1'b0)
    );

    // If IN1 and IN2 are HIGH and IN3 is LOW, Q must be HIGH.
    check_q_one_when_all_true: assert property (
        @(posedge IN1 or posedge IN2 or posedge IN3 or posedge Q) (IN1 && IN2 && !IN3) |-> (Q == 1'b1)
    );

    // If Q is HIGH, inputs must satisfy IN1 & IN2 & ~IN3.
    check_q_high_implies_inputs: assert property (
        @(posedge IN1 or posedge IN2 or posedge IN3 or posedge Q) Q |-> (IN1 && IN2 && !IN3)
    );

    // A rising Q requires IN1 and IN2 HIGH and IN3 LOW.
    check_q_rise_requires_inputs: assert property (
        @(posedge IN1 or posedge IN2 or posedge IN3 or posedge Q) $rose(Q) |-> (IN1 && IN2 && !IN3)
    );

    // A falling Q implies at least one blocking condition (!IN1 or !IN2 or IN3).
    check_q_fall_requires_block: assert property (
        @(posedge IN1 or posedge IN2 or posedge IN3 or posedge Q) $fell(Q) |-> (!IN1 || !IN2 || IN3)
    );

    // Rising IN3 forces Q LOW in the same cycle.
    check_in3_rise_forces_q_low: assert property (
        @(posedge IN1 or posedge IN2 or posedge IN3 or posedge Q) $rose(IN3) |-> (Q == 1'b0)
    );

    // Rising IN1 sets Q HIGH if IN2 HIGH and IN3 LOW.
    check_in1_rise_sets_q_if_others_true: assert property (
        @(posedge IN1 or posedge IN2 or posedge IN3 or posedge Q) ($rose(IN1) && IN2 && !IN3) |-> (Q == 1'b1)
    );

    // Rising IN2 sets Q HIGH if IN1 HIGH and IN3 LOW.
    check_in2_rise_sets_q_if_others_true: assert property (
        @(posedge IN1 or posedge IN2 or posedge IN3 or posedge Q) ($rose(IN2) && IN1 && !IN3) |-> (Q == 1'b1)
    );
endmodule