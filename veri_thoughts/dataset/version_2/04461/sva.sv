module OAI222X1_assertions (
    input logic IN1,
    input logic IN2,
    input logic IN3,
    input logic IN4,
    input logic IN5,
    input logic IN6,
    input logic QN,
    input logic QN_,
    input logic VDD,
    input logic VSS
);

    // QN matches the implemented logic equation.
    check_qn_equation: assert property (
        @($global_clock) QN == ~((IN1 & IN2) | ~(IN3 | IN4 | IN5 | IN6))
    );

    // QN_ matches the implemented logic equation.
    check_qn_bar_equation: assert property (
        @($global_clock) QN_ == ((IN1 & IN2) | ~(IN3 | IN4 | IN5 | IN6))
    );

    // The two outputs are always logical complements.
    check_outputs_complementary: assert property (
        @($global_clock) QN_ == ~QN
    );

    // IN1 and IN2 both high force QN low.
    check_and1_forces_qn_low: assert property (
        @($global_clock) (IN1 & IN2) |-> (QN == 1'b0)
    );

    // IN3 through IN6 all low force QN low.
    check_in3_to_in6_all_low_force_qn_low: assert property (
        @($global_clock) ~(IN3 | IN4 | IN5 | IN6) |-> (QN == 1'b0)
    );

    // QN is high when AND1 is low and any of IN3..IN6 is high.
    check_qn_high_condition: assert property (
        @($global_clock) ((~(IN1 & IN2)) & (IN3 | IN4 | IN5 | IN6)) |-> (QN == 1'b1)
    );

    // A high QN implies the simplified high condition holds.
    check_qn_implies_condition: assert property (
        @($global_clock) QN |-> ((~(IN1 & IN2)) & (IN3 | IN4 | IN5 | IN6))
    );

endmodule