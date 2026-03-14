module and_gate_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic Y
);
    // Output equals logical AND of inputs.
    check_and_function: assert property (
        @(posedge CLK) Y == (A & B)
    );

    // If both inputs are HIGH, output is HIGH.
    check_inputs_high_implies_y_high: assert property (
        @(posedge CLK) (A && B) |-> (Y == 1'b1)
    );

    // If A is LOW, output is LOW.
    check_a_low_forces_y_low: assert property (
        @(posedge CLK) (!A) |-> (Y == 1'b0)
    );

    // If B is LOW, output is LOW.
    check_b_low_forces_y_low: assert property (
        @(posedge CLK) (!B) |-> (Y == 1'b0)
    );

    // Output HIGH implies both inputs are HIGH.
    check_y_high_implies_inputs_high: assert property (
        @(posedge CLK) (Y == 1'b1) |-> (A && B)
    );

    // Rising edge on output requires both inputs HIGH.
    check_y_rise_requires_inputs_high: assert property (
        @(posedge CLK) $rose(Y) |-> (A && B)
    );

    // Falling edge on output implies at least one input LOW.
    check_y_fall_implies_input_low: assert property (
        @(posedge CLK) $fell(Y) |-> ((!A) || (!B))
    );

    // If inputs are stable, output is stable.
    check_stable_inputs_imply_stable_y: assert property (
        @(posedge CLK) ($stable(A) && $stable(B)) |-> $stable(Y)
    );
endmodule