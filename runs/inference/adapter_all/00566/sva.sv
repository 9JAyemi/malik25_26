module OAI21X1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // Y must match the implemented OAI21 equation.
    check_oai21_equation: assert property (
        @(posedge clk) Y == ~((A | B) & C)
    );

    // When C is low, Y must be high.
    check_c_low_forces_y_high: assert property (
        @(posedge clk) !C |-> Y
    );

    // When both OR inputs are low, Y must be high.
    check_or_inputs_low_force_y_high: assert property (
        @(posedge clk) (!A && !B) |-> Y
    );

    // When C is high and either OR input is high, Y must be low.
    check_active_c_and_active_or_input_forces_y_low: assert property (
        @(posedge clk) (C && (A || B)) |-> !Y
    );

    // A low Y requires C to be high and at least one OR input to be high.
    check_y_low_requires_active_c_and_active_or_input: assert property (
        @(posedge clk) !Y |-> (C && (A || B))
    );

    // A high Y requires C to be low or both OR inputs to be low.
    check_y_high_requires_inactive_c_or_inactive_or_inputs: assert property (
        @(posedge clk) Y |-> (!C || (!A && !B))
    );

endmodule