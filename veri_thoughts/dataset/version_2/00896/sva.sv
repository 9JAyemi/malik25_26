module NAND4X0_sva (
    input logic clk,
    input logic IN1,
    input logic IN2,
    input logic IN3,
    input logic IN4,
    input logic QN,
    input logic VDD,
    input logic VSS
);
    // QN equals (IN1&IN2) OR (IN3&IN4).
    check_qn_function: assert property (
        @(posedge clk) QN == ((IN1 & IN2) | (IN3 & IN4))
    );

    // If IN1 and IN2 are HIGH, QN must be HIGH.
    check_pair12_implies_high: assert property (
        @(posedge clk) (IN1 && IN2) |-> QN
    );

    // If IN3 and IN4 are HIGH, QN must be HIGH.
    check_pair34_implies_high: assert property (
        @(posedge clk) (IN3 && IN4) |-> QN
    );

    // If neither pair is both HIGH, QN must be LOW.
    check_both_pairs_not_high_implies_low: assert property (
        @(posedge clk) (!(IN1 && IN2) && !(IN3 && IN4)) |-> !QN
    );

    // If QN is LOW, neither pair can be both HIGH.
    check_low_implies_no_pair_high: assert property (
        @(posedge clk) !QN |-> (!(IN1 && IN2) && !(IN3 && IN4))
    );

    // If QN is HIGH, at least one pair is both HIGH.
    check_high_implies_some_pair_high: assert property (
        @(posedge clk) QN |-> ((IN1 && IN2) || (IN3 && IN4))
    );

    // If all four inputs are stable, QN must be stable (pure combinational).
    check_stability_with_stable_inputs: assert property (
        @(posedge clk) $stable({IN1,IN2,IN3,IN4}) |-> $stable(QN)
    );

    // QN changes only if at least one of the four inputs changes.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) $changed(QN) |-> !$stable({IN1,IN2,IN3,IN4})
    );

    // Changes on VDD/VSS do not affect QN when data inputs are stable.
    check_power_pins_no_effect: assert property (
        @(posedge clk) ($changed(VDD) || $changed(VSS)) && $stable({IN1,IN2,IN3,IN4}) |-> $stable(QN)
    );

    // If all inputs are LOW, QN must be LOW.
    check_all_zero_implies_low: assert property (
        @(posedge clk) (!IN1 && !IN2 && !IN3 && !IN4) |-> !QN
    );
endmodule