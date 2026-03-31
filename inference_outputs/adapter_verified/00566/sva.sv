module OAI21X1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

// Y must match the implemented OAI21 function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~((A | B) & C)
    );

// When C is low, Y must be high.
    check_c_low_forces_y_high: assert property (
        @(posedge clk) !C |-> Y
    );

// When both A and B are low, Y must be high.
    check_ab_low_forces_y_high: assert property (
        @(posedge clk) (!A && !B) |-> Y
    );

// When A is high and C is high, Y must be low.
    check_a_high_c_high_forces_y_low: assert property (
        @(posedge clk) (A && C) |-> !Y
    );

// When B is high and C is high, Y must be low.
    check_b_high_c_high_forces_y_low: assert property (
        @(posedge clk) (B && C) |-> !Y
    );

// A high Y requires C to be high.
    check_y_high_requires_c_high: assert property (
        @(posedge clk) Y |-> C
    );

// A high Y requires at least one of A or B to be low.
    check_y_high_requires_ab_low: assert property (
        @(posedge clk) Y |-> (!A || !B)
    );

endmodule
