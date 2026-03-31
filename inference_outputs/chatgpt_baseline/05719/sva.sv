module and_gate_extra_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // Y implements A & B & ~C.
    check_output_function: assert property (
        @(posedge clk) Y == (A & B & ~C)
    );

    // Y can only be high when A and B are high and C is low.
    check_y_high_requires_inputs: assert property (
        @(posedge clk) Y |-> (A && B && !C)
    );

    // A low forces Y low.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) !A |-> !Y
    );

    // B low forces Y low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) !B |-> !Y
    );

    // C high forces Y low.
    check_c_high_forces_y_low: assert property (
        @(posedge clk) C |-> !Y
    );

    // A and B high with C low forces Y high.
    check_all_true_inputs_drive_y_high: assert property (
        @(posedge clk) (A && B && !C) |-> Y
    );

    // With A and B high, Y equals the inverse of C.
    check_ab_high_makes_y_follow_not_c: assert property (
        @(posedge clk) (A && B) |-> (Y == !C)
    );

    // With C low, Y matches A AND B.
    check_c_low_makes_y_follow_a_and_b: assert property (
        @(posedge clk) !C |-> (Y == (A & B))
    );

endmodule