module OAI21X1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // Y must match the implemented OAI21X1 equation.
    check_oai21x1_equation: assert property (
        @(posedge clk) Y == ~((A | B) & C)
    );

    // When C is low, the AND term is low and Y must be high.
    check_c_low_forces_y_high: assert property (
        @(posedge clk) !C |-> Y
    );

    // When both OR inputs are low, the OR term is low and Y must be high.
    check_ab_low_forces_y_high: assert property (
        @(posedge clk) (!A && !B) |-> Y
    );

    // When C is high and either OR input is high, Y must be low.
    check_c_high_and_ab_high_forces_y_low: assert property (
        @(posedge clk) (C && (A || B)) |-> !Y
    );

    // A low Y can only occur when C is high and at least one OR input is high.
    check_y_low_only_when_c_high_and_ab_high: assert property (
        @(posedge clk) !Y |-> (C && (A || B))
    );

endmodule