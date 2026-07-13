module nand4_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);
    // When all inputs are 1, Y must be 0 (NAND truth).
    check_all_ones_implies_y_zero: assert property (
        @(posedge clk) ((A===1'b1) && (B===1'b1) && (C===1'b1) && (D===1'b1)) |-> (Y===1'b0)
    );

    // If A is 0, Y must be 1 (NAND short-circuit).
    check_a_zero_implies_y_one: assert property (
        @(posedge clk) (A===1'b0) |-> (Y===1'b1)
    );

    // If B is 0, Y must be 1 (NAND short-circuit).
    check_b_zero_implies_y_one: assert property (
        @(posedge clk) (B===1'b0) |-> (Y===1'b1)
    );

    // If C is 0, Y must be 1 (NAND short-circuit).
    check_c_zero_implies_y_one: assert property (
        @(posedge clk) (C===1'b0) |-> (Y===1'b1)
    );

    // If D is 0, Y must be 1 (NAND short-circuit).
    check_d_zero_implies_y_one: assert property (
        @(posedge clk) (D===1'b0) |-> (Y===1'b1)
    );

    // Y is 0 only when all inputs are 1 (NAND iff).
    check_y_zero_implies_all_ones: assert property (
        @(posedge clk) (Y===1'b0) |-> ((A===1'b1) && (B===1'b1) && (C===1'b1) && (D===1'b1))
    );

    // Y=1 implies at least one input is not 1.
    check_y_one_implies_not_all_ones: assert property (
        @(posedge clk) (Y===1'b1) |-> ((A!==1'b1) || (B!==1'b1) || (C!==1'b1) || (D!==1'b1))
    );

    // Y cannot rise unless some input changed.
    check_y_rise_requires_input_change: assert property (
        @(posedge clk) $rose(Y) |-> !$stable({A,B,C,D})
    );

    // Y cannot fall unless some input changed.
    check_y_fall_requires_input_change: assert property (
        @(posedge clk) $fell(Y) |-> !$stable({A,B,C,D})
    );

    // Y falling implies all inputs are 1 in the new cycle.
    check_y_fall_implies_all_ones: assert property (
        @(posedge clk) $fell(Y) |-> ((A===1'b1) && (B===1'b1) && (C===1'b1) && (D===1'b1))
    );

    // Y rising implies not all inputs are 1 in the new cycle.
    check_y_rise_implies_not_all_ones: assert property (
        @(posedge clk) $rose(Y) |-> !((A===1'b1) && (B===1'b1) && (C===1'b1) && (D===1'b1))
    );

    // If inputs are stable across a cycle, Y must remain stable.
    check_stable_inputs_imply_stable_y: assert property (
        @(posedge clk) $stable({A,B,C,D}) |-> $stable(Y)
    );
endmodule