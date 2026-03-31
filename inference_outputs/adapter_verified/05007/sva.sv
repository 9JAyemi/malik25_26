module nor_gate_using_nand_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out
);

// Output equals NOR of inputs.
    check_function_equivalence: assert property (
        @(posedge clk) out == ~(a | b)
    );

// When both inputs are 0, output is 1.
    check_both_zero_high: assert property (
        @(posedge clk) (!a && !b) |-> (out == 1'b1)
    );

// When a is 0, output equals ~b.
    check_a_zero_equals_not_b: assert property (
        @(posedge clk) (!a) |-> (out == ~b)
    );

// When b is 0, output equals ~a.
    check_b_zero_equals_not_a: assert property (
        @(posedge clk) (!b) |-> (out == ~a)
    );

// When both inputs are 1, output is 0.
    check_both_one_low: assert property (
        @(posedge clk) (a && b) |-> (out == 1'b0)
    );

// Rising a forces output low in the same cycle.
    check_a_rise_forces_low: assert property (
        @(posedge clk) $rose(a) |-> (out == 1'b0)
    );

// Rising b forces output low in the same cycle.
    check_b_rise_forces_low: assert property (
        @(posedge clk) $rose(b) |-> (out == 1'b0)
    );

// Falling a makes output high in the same cycle.
    check_a_fall_forces_high: assert property (
        @(posedge clk) $fell(a) |-> (out == 1'b1)
    );

// Falling b makes output high in the same cycle.
    check_b_fall_forces_high: assert property (
        @(posedge clk) $fell(b) |-> (out == 1'b1)
    );

endmodule
