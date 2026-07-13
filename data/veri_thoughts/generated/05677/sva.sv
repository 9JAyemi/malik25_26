module mux_2_1_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic S
);

    // Y must implement the mux equation.
    check_mux_equation: assert property (
        @(posedge clk) Y == ((A & ~S) | (B & S))
    );

    // When S is low, Y must equal A.
    check_select_a_when_s_low: assert property (
        @(posedge clk) !S |-> (Y == A)
    );

    // When S is high, Y must equal B.
    check_select_b_when_s_high: assert property (
        @(posedge clk) S |-> (Y == B)
    );

    // If both inputs are low, Y must be low.
    check_both_inputs_low: assert property (
        @(posedge clk) (!A && !B) |-> !Y
    );

    // If both inputs are high, Y must be high.
    check_both_inputs_high: assert property (
        @(posedge clk) (A && B) |-> Y
    );

    // If A is low and B is high, Y must follow S.
    check_low_high_case: assert property (
        @(posedge clk) (!A && B) |-> (Y == S)
    );

    // If A is high and B is low, Y must follow inverted S.
    check_high_low_case: assert property (
        @(posedge clk) (A && !B) |-> (Y == ~S)
    );

endmodule