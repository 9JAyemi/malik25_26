module sky130_fd_sc_hdll__o21ai_sva (
    input  logic clk,  // External sampling clock (RTL has no clock/reset)
    input  logic Y,
    input  logic A1,
    input  logic A2,
    input  logic B1
);
    // Y implements ~((A1 | A2) & B1).
    check_functional_equation: assert property (
        @(posedge clk) disable iff (1'b0) Y == ~(B1 & (A1 | A2))
    );

    // If B1 is LOW, Y must be HIGH.
    check_y_high_when_b1_low: assert property (
        @(posedge clk) disable iff (1'b0) (!B1) |-> (Y == 1'b1)
    );

    // If either A1 or A2 is HIGH while B1 is HIGH, Y must be LOW.
    check_y_low_when_b1_and_any_a: assert property (
        @(posedge clk) disable iff (1'b0) (B1 && (A1 || A2)) |-> (Y == 1'b0)
    );

    // If both A1 and A2 are LOW, Y must be HIGH (independent of B1).
    check_y_high_when_both_a_low: assert property (
        @(posedge clk) disable iff (1'b0) (!A1 && !A2) |-> (Y == 1'b1)
    );

    // Y can only be LOW if B1 is HIGH and at least one of A1/A2 is HIGH.
    check_y_zero_implies_b1_and_any_a: assert property (
        @(posedge clk) disable iff (1'b0) (Y == 1'b0) |-> (B1 && (A1 || A2))
    );

    // If Y is HIGH, then either B1 is LOW or both A1 and A2 are LOW.
    check_y_one_implies_not_b1_or_both_a_low: assert property (
        @(posedge clk) disable iff (1'b0) (Y == 1'b1) |-> ((!B1) || (!A1 && !A2))
    );

    // With B1 HIGH, a rising edge on A1 forces Y LOW.
    check_y_zero_on_a1_rise_with_b1: assert property (
        @(posedge clk) disable iff (1'b0) (B1 && $rose(A1)) |-> (Y == 1'b0)
    );

    // With B1 HIGH, a rising edge on A2 forces Y LOW.
    check_y_zero_on_a2_rise_with_b1: assert property (
        @(posedge clk) disable iff (1'b0) (B1 && $rose(A2)) |-> (Y == 1'b0)
    );

    // A falling edge on B1 forces Y HIGH.
    check_y_one_on_b1_fall: assert property (
        @(posedge clk) disable iff (1'b0) $fell(B1) |-> (Y == 1'b1)
    );

    // If all inputs are stable across a cycle, Y must be stable.
    check_y_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(A1) && $stable(A2) && $stable(B1)) |-> $stable(Y)
    );
endmodule