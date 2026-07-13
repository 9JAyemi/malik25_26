module comparator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic EQ,
    input logic GT
);

// EQ must match the 4-input equality function.
    check_eq_definition: assert property (
        @(posedge clk) EQ == ((A == B) && (B == C) && (C == D))
    );

// GT must match the implemented greater-or-equal function.
    check_gt_definition: assert property (
        @(posedge clk) GT == ((A > B) || ((A == B) && (C > D)))
    );

// If A is greater than B, GT must be high.
    check_gt_when_a_greater_b: assert property (
        @(posedge clk) (A > B) |-> GT
    );

// If A equals B and C is greater than D, GT must be high.
    check_gt_when_a_eq_b_and_c_greater_d: assert property (
        @(posedge clk) ((A == B) && (C > D)) |-> GT
    );

// If A is less than B, GT must be low.
    check_gt_low_when_a_less_b: assert property (
        @(posedge clk) (A < B) |-> !GT
    );

// If A equals B and C equals D, GT must be high.
    check_gt_high_when_a_eq_b_and_c_eq_d: assert property (
        @(posedge clk) ((A == B) && (C == D)) |-> GT
    );

// If A equals B and C equals D, EQ must be high.
    check_eq_high_when_a_eq_b_and_c_eq_d: assert property (
        @(posedge clk) ((A == B) && (C == D)) |-> EQ
    );

// If A is not equal to B, EQ must be low.
    check_eq_low_when_a_ne_b: assert property (
        @(posedge clk) (A != B) |-> !EQ
    );

// If C is not equal to D, GT must be low.
    check_gt_low_when_c_ne_d: assert property (
        @(posedge clk) (C != D) |-> !GT
    );

endmodule
