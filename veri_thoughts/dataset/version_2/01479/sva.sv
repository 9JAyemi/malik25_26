module logic_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // Y equals NOR of B1 and (A1 & A2).
    check_func_equation: assert property (
        @(posedge clk) Y == ~(B1 | (A1 & A2))
    );

    // If B1 is HIGH then Y must be LOW.
    check_y_low_when_b1_high: assert property (
        @(posedge clk) (B1 == 1'b1) |-> (Y == 1'b0)
    );

    // If A1 and A2 are both HIGH then Y must be LOW.
    check_y_low_when_a1a2_high: assert property (
        @(posedge clk) ((A1 == 1'b1) && (A2 == 1'b1)) |-> (Y == 1'b0)
    );

    // If B1 is LOW and A1 is LOW then Y must be HIGH (independent of A2).
    check_y_high_when_b1_low_a1_low: assert property (
        @(posedge clk) ((B1 == 1'b0) && (A1 == 1'b0)) |-> (Y == 1'b1)
    );

    // If B1 is LOW and A2 is LOW then Y must be HIGH (independent of A1).
    check_y_high_when_b1_low_a2_low: assert property (
        @(posedge clk) ((B1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // If A1 and A2 are both LOW then Y equals ~B1.
    check_y_equals_not_b1_when_a1a2_zero: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == ~B1)
    );

    // If Y is HIGH then B1 is LOW and not both A1 and A2 are HIGH.
    check_y_one_implies_conditions: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((B1 == 1'b0) && !((A1 == 1'b1) && (A2 == 1'b1)))
    );

    // If B1 is LOW and Y is LOW then A1 and A2 must both be HIGH.
    check_y_zero_with_b1_zero_implies_a1a2: assert property (
        @(posedge clk) ((B1 == 1'b0) && (Y == 1'b0)) |-> ((A1 == 1'b1) && (A2 == 1'b1))
    );

    // Output is stable when inputs are stable across a cycle.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({A1, A2, B1}) |-> $stable(Y)
    );

    // De Morgan equivalent form of the function.
    check_demorgan_form: assert property (
        @(posedge clk) Y == ((~B1) & ((~A1) | (~A2)))
    );

endmodule