module and_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Y
);
    // DUT is purely combinational with no reset; assertions sample on external clk.

    // Y equals bitwise AND of A and B.
    check_and_function: assert property (
        @(posedge clk) (Y === (A & B))
    );

    // When both inputs are HIGH, Y is HIGH.
    check_both_high_implies_y_high: assert property (
        @(posedge clk) ((A === 1'b1) && (B === 1'b1)) |-> (Y === 1'b1)
    );

    // If any input is LOW, Y is LOW.
    check_any_low_implies_y_low: assert property (
        @(posedge clk) ((A === 1'b0) || (B === 1'b0)) |-> (Y === 1'b0)
    );

    // Y can be HIGH only if both inputs are HIGH.
    check_y_high_requires_both_high: assert property (
        @(posedge clk) (Y === 1'b1) |-> ((A === 1'b1) && (B === 1'b1))
    );

    // Y being LOW implies at least one input is LOW.
    check_y_low_requires_some_input_low: assert property (
        @(posedge clk) (Y === 1'b0) |-> ((A === 1'b0) || (B === 1'b0))
    );

    // A rising edge with B HIGH causes Y to rise.
    check_a_rise_with_b_high_causes_y_rise: assert property (
        @(posedge clk) ($rose(A) && (B === 1'b1)) |-> $rose(Y)
    );

    // B rising edge with A HIGH causes Y to rise.
    check_b_rise_with_a_high_causes_y_rise: assert property (
        @(posedge clk) ($rose(B) && (A === 1'b1)) |-> $rose(Y)
    );

    // Y can only rise when both inputs are HIGH.
    check_y_rose_requires_inputs1: assert property (
        @(posedge clk) $rose(Y) |-> ((A === 1'b1) && (B === 1'b1))
    );

    // A falling from HIGH with B previously HIGH causes Y to fall.
    check_a_fall_with_pastb1_causes_y_fall: assert property (
        @(posedge clk) ($fell(A) && ($past(B) === 1'b1)) |-> $fell(Y)
    );

    // B falling from HIGH with A previously HIGH causes Y to fall.
    check_b_fall_with_pasta1_causes_y_fall: assert property (
        @(posedge clk) ($fell(B) && ($past(A) === 1'b1)) |-> $fell(Y)
    );

    // A Y falling edge must be caused by a falling input.
    check_y_fall_caused_by_input_fall: assert property (
        @(posedge clk) $fell(Y) |-> ($fell(A) || $fell(B))
    );

    // If inputs are stable, output is stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(Y)
    );
endmodule