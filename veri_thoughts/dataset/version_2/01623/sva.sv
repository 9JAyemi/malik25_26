module and_gate_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    // Y must be 1 when all inputs are 1.
    check_all_inputs_high_implies_Y_high: assert property (
        @(posedge clk) disable iff (1'b0) (A1 && A2 && B1 && C1) |-> (Y == 1'b1)
    );
    // Y can be 1 only if all inputs are 1.
    check_Y_high_implies_all_inputs_high: assert property (
        @(posedge clk) disable iff (1'b0) (Y == 1'b1) |-> (A1 && A2 && B1 && C1)
    );
    // If any input is 0, Y must be 0.
    check_any_input_low_forces_Y_low: assert property (
        @(posedge clk) disable iff (1'b0) (!A1 || !A2 || !B1 || !C1) |-> (Y == 1'b0)
    );
    // If Y rises, all inputs must be 1 now.
    check_Y_rose_requires_all_inputs_high: assert property (
        @(posedge clk) disable iff (1'b0) $rose(Y) |-> (A1 && A2 && B1 && C1)
    );
    // If Y falls, at least one input must be 0 now.
    check_Y_fell_requires_some_input_low: assert property (
        @(posedge clk) disable iff (1'b0) $fell(Y) |-> (!A1 || !A2 || !B1 || !C1)
    );
    // If A1 falls to 0, Y must be 0 now.
    check_A1_fall_forces_Y_low: assert property (
        @(posedge clk) disable iff (1'b0) $fell(A1) |-> (Y == 1'b0)
    );
    // If A2 falls to 0, Y must be 0 now.
    check_A2_fall_forces_Y_low: assert property (
        @(posedge clk) disable iff (1'b0) $fell(A2) |-> (Y == 1'b0)
    );
    // If B1 falls to 0, Y must be 0 now.
    check_B1_fall_forces_Y_low: assert property (
        @(posedge clk) disable iff (1'b0) $fell(B1) |-> (Y == 1'b0)
    );
    // If C1 falls to 0, Y must be 0 now.
    check_C1_fall_forces_Y_low: assert property (
        @(posedge clk) disable iff (1'b0) $fell(C1) |-> (Y == 1'b0)
    );
    // When A1 is the last input to rise, Y must rise.
    check_last_bit_rise_A1_causes_Y_rise: assert property (
        @(posedge clk) disable iff (1'b0) ($rose(A1) && A2 && B1 && C1) |-> $rose(Y)
    );
endmodule