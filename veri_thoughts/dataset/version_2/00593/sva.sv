module nand2_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B
);
    // Output equals A & B.
    check_and_function: assert property (
        @(posedge clk) disable iff (1'b0) (Y == (A & B))
    );

    // If either input is 0, output must be 0.
    check_zero_if_any_zero: assert property (
        @(posedge clk) disable iff (1'b0) ((A == 1'b0) || (B == 1'b0)) |-> (Y == 1'b0)
    );

    // If both inputs are 1, output must be 1.
    check_one_if_both_one: assert property (
        @(posedge clk) disable iff (1'b0) ((A == 1'b1) && (B == 1'b1)) |-> (Y == 1'b1)
    );

    // When B is 1, output follows A.
    check_output_eq_A_when_B_high: assert property (
        @(posedge clk) disable iff (1'b0) (B == 1'b1) |-> (Y == A)
    );

    // When A is 1, output follows B.
    check_output_eq_B_when_A_high: assert property (
        @(posedge clk) disable iff (1'b0) (A == 1'b1) |-> (Y == B)
    );

    // If inputs are stable, output must be stable.
    check_stability_with_stable_inputs: assert property (
        @(posedge clk) disable iff (1'b0) $stable(A) && $stable(B) |-> $stable(Y)
    );

    // Output change only occurs if at least one input changes.
    check_output_change_needs_input_change: assert property (
        @(posedge clk) disable iff (1'b0) $changed(Y) |-> ($changed(A) || $changed(B))
    );

    // A rising output requires both inputs high and at least one rising.
    check_y_rise_requires_inputs_and_one_rise: assert property (
        @(posedge clk) disable iff (1'b0) $rose(Y) |-> (A == 1'b1) && (B == 1'b1) && ($rose(A) || $rose(B))
    );

    // If A rises while B is high, Y must rise.
    check_y_rise_when_A_rises_B_high: assert property (
        @(posedge clk) disable iff (1'b0) $rose(A) && (B == 1'b1) |-> $rose(Y)
    );

    // If B rises while A is high, Y must rise.
    check_y_rise_when_B_rises_A_high: assert property (
        @(posedge clk) disable iff (1'b0) $rose(B) && (A == 1'b1) |-> $rose(Y)
    );

    // A falling output requires at least one input to fall.
    check_y_fall_requires_one_input_fall: assert property (
        @(posedge clk) disable iff (1'b0) $fell(Y) |-> ($fell(A) || $fell(B))
    );
endmodule