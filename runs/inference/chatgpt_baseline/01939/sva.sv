module my_module_sva (
    input logic CLK,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X
);
    // X implements A1 & A2 & ~(B1 & B2).
    check_x_equation: assert property (
        @(posedge CLK) X == (A1 & A2 & ~(B1 & B2))
    );

    // If A1 is LOW then X must be LOW.
    check_x_zero_when_a1_low: assert property (
        @(posedge CLK) (!A1) |-> (X == 1'b0)
    );

    // If A2 is LOW then X must be LOW.
    check_x_zero_when_a2_low: assert property (
        @(posedge CLK) (!A2) |-> (X == 1'b0)
    );

    // If both B1 and B2 are HIGH then X must be LOW.
    check_x_zero_when_b1b2_high: assert property (
        @(posedge CLK) (B1 & B2) |-> (X == 1'b0)
    );

    // If A1&A2 are HIGH and not(B1&B2) then X must be HIGH.
    check_x_one_when_a_high_and_notb: assert property (
        @(posedge CLK) (A1 & A2 & ~(B1 & B2)) |-> (X == 1'b1)
    );

    // If X is HIGH then A1&A2 are HIGH and not(B1&B2).
    check_x_one_implies_a_high_and_notb: assert property (
        @(posedge CLK) (X == 1'b1) |-> (A1 & A2 & ~(B1 & B2))
    );

    // If X is LOW then either A1 or A2 is LOW, or B1&B2 are HIGH.
    check_x_zero_implies_causes: assert property (
        @(posedge CLK) (X == 1'b0) |-> ((!A1) || (!A2) || (B1 & B2))
    );

    // When A1&A2 are HIGH, X equals ~(B1&B2).
    check_x_equals_notb_when_a_high: assert property (
        @(posedge CLK) (A1 & A2) |-> (X == ~(B1 & B2))
    );

    // When B1&B2 are LOW, X equals A1&A2.
    check_x_equals_a_when_b_low: assert property (
        @(posedge CLK) (~(B1 & B2)) |-> (X == (A1 & A2))
    );
endmodule