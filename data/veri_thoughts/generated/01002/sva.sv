module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic CI,
    input logic SUM,
    input logic COUT_N
);
    // SUM must equal A ^ B ^ CI.
    check_sum_is_xor: assert property (
        @(posedge clk) disable iff (1'b0) SUM == (A ^ B ^ CI)
    );

    // COUT_N must equal complement of majority (two-or-more ones).
    check_coutn_is_comp_majority: assert property (
        @(posedge clk) disable iff (1'b0) COUT_N == ~((A & B) | (A & CI) | (B & CI))
    );

    // If all inputs are stable over a cycle, outputs must be stable too.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(A) && $stable(B) && $stable(CI)) |-> ($stable(SUM) && $stable(COUT_N))
    );

    // With B and CI stable, toggling A must toggle SUM.
    check_sum_toggles_on_A_toggle: assert property (
        @(posedge clk) disable iff (1'b0) ($changed(A) && $stable(B) && $stable(CI)) |-> $changed(SUM)
    );

    // With A and CI stable, toggling B must toggle SUM.
    check_sum_toggles_on_B_toggle: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(A) && $changed(B) && $stable(CI)) |-> $changed(SUM)
    );

    // With A and B stable, toggling CI must toggle SUM.
    check_sum_toggles_on_CI_toggle: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(A) && $stable(B) && $changed(CI)) |-> $changed(SUM)
    );

    // Truth table: 000 -> SUM=0, COUT_N=1.
    truth_000: assert property (
        @(posedge clk) disable iff (1'b0) (A==1'b0 && B==1'b0 && CI==1'b0) |-> (SUM==1'b0 && COUT_N==1'b1)
    );

    // Truth table: 001 -> SUM=1, COUT_N=1.
    truth_001: assert property (
        @(posedge clk) disable iff (1'b0) (A==1'b0 && B==1'b0 && CI==1'b1) |-> (SUM==1'b1 && COUT_N==1'b1)
    );

    // Truth table: 011 -> SUM=0, COUT_N=0.
    truth_011: assert property (
        @(posedge clk) disable iff (1'b0) (A==1'b0 && B==1'b1 && CI==1'b1) |-> (SUM==1'b0 && COUT_N==1'b0)
    );

    // Truth table: 111 -> SUM=1, COUT_N=0.
    truth_111: assert property (
        @(posedge clk) disable iff (1'b0) (A==1'b1 && B==1'b1 && CI==1'b1) |-> (SUM==1'b1 && COUT_N==1'b0)
    );
endmodule