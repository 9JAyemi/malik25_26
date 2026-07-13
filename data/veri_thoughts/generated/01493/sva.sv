module logic_module_sva (
    // DUT ports as inputs
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    // Sampling clock (RTL has no clock/reset; this is used only for property sampling)
    input logic clk
);

    // Y matches NOR of B1,C1,D1 and AND of A1&A2.
    check_function_equivalence: assert property (
        @(posedge clk) Y === ~(B1 | C1 | D1 | (A1 & A2))
    );

    // If Y is HIGH, then B1,C1,D1 are LOW and not both A1 and A2 are HIGH.
    check_y_high_implies_inputs_low: assert property (
        @(posedge clk) (Y === 1'b1) |-> ((B1 === 1'b0) && (C1 === 1'b0) && (D1 === 1'b0) && ((A1 === 1'b0) || (A2 === 1'b0)))
    );

    // If B1 is HIGH, Y must be LOW.
    check_b1_high_forces_y_low: assert property (
        @(posedge clk) (B1 === 1'b1) |-> (Y === 1'b0)
    );

    // If C1 is HIGH, Y must be LOW.
    check_c1_high_forces_y_low: assert property (
        @(posedge clk) (C1 === 1'b1) |-> (Y === 1'b0)
    );

    // If D1 is HIGH, Y must be LOW.
    check_d1_high_forces_y_low: assert property (
        @(posedge clk) (D1 === 1'b1) |-> (Y === 1'b0)
    );

    // If both A1 and A2 are HIGH, Y must be LOW.
    check_a1a2_both_high_forces_y_low: assert property (
        @(posedge clk) ((A1 === 1'b1) && (A2 === 1'b1)) |-> (Y === 1'b0)
    );

    // If B1,C1,D1 are LOW and A1 is LOW, Y must be HIGH (independent of A2).
    check_all_low_with_a1_low_gives_y_high: assert property (
        @(posedge clk) ((B1 === 1'b0) && (C1 === 1'b0) && (D1 === 1'b0) && (A1 === 1'b0)) |-> (Y === 1'b1)
    );

    // If B1,C1,D1 are LOW and A2 is LOW, Y must be HIGH (independent of A1).
    check_all_low_with_a2_low_gives_y_high: assert property (
        @(posedge clk) ((B1 === 1'b0) && (C1 === 1'b0) && (D1 === 1'b0) && (A2 === 1'b0)) |-> (Y === 1'b1)
    );

    // If B1,C1,D1 are LOW and not(A1&A2), Y must be HIGH.
    check_y_high_when_no_ors_and_no_and: assert property (
        @(posedge clk) ((B1 === 1'b0) && (C1 === 1'b0) && (D1 === 1'b0) && !((A1 === 1'b1) && (A2 === 1'b1))) |-> (Y === 1'b1)
    );

    // If inputs are stable between cycles, Y is stable between cycles.
    check_stability_with_stable_inputs: assert property (
        @(posedge clk) $stable({A1,A2,B1,C1,D1}) |-> $stable(Y)
    );

endmodule