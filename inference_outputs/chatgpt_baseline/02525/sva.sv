module digital_circuit_sva (
    input logic CLK,          // External sampling clock (DUT has no clock/reset)
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N,
    // Internal nets exposed via bind (optional)
    input logic b,
    input logic and0_out,
    input logic nor0_out_Y
);
    // Pure combinational DUT: Y = ~(~B1_N | (A1 & A2)); no resets present.

    // Y implements the Boolean function from inputs.
    check_output_function: assert property (
        @(posedge CLK) disable iff (1'b0) Y === ~( (~B1_N) | (A1 & A2) )
    );

    // not gate: b = ~B1_N.
    check_not_gate: assert property (
        @(posedge CLK) disable iff (1'b0) b === ~B1_N
    );

    // and gate: and0_out = A1 & A2.
    check_and_gate: assert property (
        @(posedge CLK) disable iff (1'b0) and0_out === (A1 & A2)
    );

    // nor gate: nor0_out_Y = ~(b | and0_out).
    check_nor_gate: assert property (
        @(posedge CLK) disable iff (1'b0) nor0_out_Y === ~(b | and0_out)
    );

    // buffer: Y = nor0_out_Y.
    check_buffer: assert property (
        @(posedge CLK) disable iff (1'b0) Y === nor0_out_Y
    );

    // If B1_N is 0, Y must be 0.
    check_b1n_low_forces_y_low: assert property (
        @(posedge CLK) disable iff (1'b0) (B1_N === 1'b0) |-> (Y === 1'b0)
    );

    // If both A1 and A2 are 1, Y must be 0.
    check_both_a_high_forces_y_low: assert property (
        @(posedge CLK) disable iff (1'b0) ((A1 === 1'b1) && (A2 === 1'b1)) |-> (Y === 1'b0)
    );

    // If B1_N is 1 and A1 is 0, Y must be 1.
    check_b1n_high_a1_low_sets_y_high: assert property (
        @(posedge CLK) disable iff (1'b0) ((B1_N === 1'b1) && (A1 === 1'b0)) |-> (Y === 1'b1)
    );

    // If B1_N is 1 and A2 is 0, Y must be 1.
    check_b1n_high_a2_low_sets_y_high: assert property (
        @(posedge CLK) disable iff (1'b0) ((B1_N === 1'b1) && (A2 === 1'b0)) |-> (Y === 1'b1)
    );

    // If Y is 1, then B1_N is 1 and not (A1 & A2).
    check_y_high_implies_inputs: assert property (
        @(posedge CLK) disable iff (1'b0) (Y === 1'b1) |-> ((B1_N === 1'b1) && !((A1 === 1'b1) && (A2 === 1'b1)))
    );

    // If inputs are stable, Y must be stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0) $stable({A1, A2, B1_N}) |-> $stable(Y)
    );

    // If B1_N is stable, b must be stable.
    check_b_stable_when_b1n_stable: assert property (
        @(posedge CLK) disable iff (1'b0) $stable(B1_N) |-> $stable(b)
    );

    // If A1 and A2 are stable, and0_out must be stable.
    check_and0_out_stable_when_a_stable: assert property (
        @(posedge CLK) disable iff (1'b0) $stable({A1, A2}) |-> $stable(and0_out)
    );

    // If b and and0_out are stable, nor0_out_Y must be stable.
    check_nor0_out_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0) $stable({b, and0_out}) |-> $stable(nor0_out_Y)
    );
endmodule