module four_input_logic_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Z
);

    // Z matches the RTL's nested conditional expression.
    check_z_matches_rtl_expression: assert property (
        @(posedge clk)
        Z == ((A & ~B) ? 1'b1 : ((~A & B) ? 1'b0 : ((A & B) ? C : D)))
    );

    // When A is high and B is low, Z is forced high.
    check_a1_b0_forces_z_high: assert property (
        @(posedge clk)
        (A && !B) |-> (Z == 1'b1)
    );

    // When A is low and B is high, Z is forced low.
    check_a0_b1_forces_z_low: assert property (
        @(posedge clk)
        (!A && B) |-> (Z == 1'b0)
    );

    // When both A and B are high, Z follows C.
    check_a1_b1_selects_c: assert property (
        @(posedge clk)
        (A && B) |-> (Z == C)
    );

    // When both A and B are low, Z follows D.
    check_a0_b0_selects_d: assert property (
        @(posedge clk)
        (!A && !B) |-> (Z == D)
    );

endmodule