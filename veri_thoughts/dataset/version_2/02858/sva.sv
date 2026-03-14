module nor3_sva (
    input logic clk,  // sampling clock for SVA (DUT has no clock/reset)
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);
    // Y implements a 3-input NOR of A,B,C.
    check_function_equivalence: assert property (
        @(posedge clk) Y === ~(A | B | C)
    );

    // Any input HIGH forces Y LOW.
    check_any_input_one_forces_y_zero: assert property (
        @(posedge clk) ((A===1'b1) || (B===1'b1) || (C===1'b1)) |-> (Y===1'b0)
    );

    // All inputs LOW force Y HIGH.
    check_all_inputs_zero_forces_y_one: assert property (
        @(posedge clk) ((A===1'b0) && (B===1'b0) && (C===1'b0)) |-> (Y===1'b1)
    );

    // If Y is HIGH, all inputs must be LOW.
    check_y_high_implies_all_inputs_low: assert property (
        @(posedge clk) (Y===1'b1) |-> ((A===1'b0) && (B===1'b0) && (C===1'b0))
    );

    // If Y is LOW, at least one input must be HIGH.
    check_y_low_implies_any_input_high: assert property (
        @(posedge clk) (Y===1'b0) |-> ((A===1'b1) || (B===1'b1) || (C===1'b1))
    );

    // On Y rising, all inputs must be LOW.
    check_output_rise_requires_all_inputs_zero: assert property (
        @(posedge clk) $rose(Y) |-> ((A===1'b0) && (B===1'b0) && (C===1'b0))
    );

    // On Y falling, at least one input must be HIGH.
    check_output_fall_requires_any_input_one: assert property (
        @(posedge clk) $fell(Y) |-> ((A===1'b1) || (B===1'b1) || (C===1'b1))
    );

    // If inputs are stable between cycles, Y is stable too.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) ((A === $past(A)) && (B === $past(B)) && (C === $past(C))) |-> (Y === $past(Y))
    );

    // If A rises and B,C are 0 both before and after, Y must fall.
    check_y_fall_when_A_rises_and_others_zero: assert property (
        @(posedge clk) ($rose(A) && (B===1'b0) && (C===1'b0) && $past(B===1'b0) && $past(C===1'b0)) |-> $fell(Y)
    );

    // If B rises and A,C are 0 both before and after, Y must fall.
    check_y_fall_when_B_rises_and_others_zero: assert property (
        @(posedge clk) ($rose(B) && (A===1'b0) && (C===1'b0) && $past(A===1'b0) && $past(C===1'b0)) |-> $fell(Y)
    );

    // If C rises and A,B are 0 both before and after, Y must fall.
    check_y_fall_when_C_rises_and_others_zero: assert property (
        @(posedge clk) ($rose(C) && (A===1'b0) && (B===1'b0) && $past(A===1'b0) && $past(B===1'b0)) |-> $fell(Y)
    );

    // If A falls and B,C are 0 both before and after, Y must rise.
    check_y_rise_when_A_falls_and_others_zero: assert property (
        @(posedge clk) ($fell(A) && (B===1'b0) && (C===1'b0) && $past(B===1'b0) && $past(C===1'b0)) |-> $rose(Y)
    );

    // If B falls and A,C are 0 both before and after, Y must rise.
    check_y_rise_when_B_falls_and_others_zero: assert property (
        @(posedge clk) ($fell(B) && (A===1'b0) && (C===1'b0) && $past(A===1'b0) && $past(C===1'b0)) |-> $rose(Y)
    );

    // If C falls and A,B are 0 both before and after, Y must rise.
    check_y_rise_when_C_falls_and_others_zero: assert property (
        @(posedge clk) ($fell(C) && (A===1'b0) && (B===1'b0) && $past(A===1'b0) && $past(B===1'b0)) |-> $rose(Y)
    );
endmodule