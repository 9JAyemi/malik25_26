module and_gate_sva (
    input logic clk,     // sampling clock (environment-provided)
    input logic a,
    input logic b,
    input logic out
);
    // Output equals logical AND of inputs (4-state aware).
    check_out_equals_and: assert property (
        @(posedge clk) out === (a & b)
    );

    // When both inputs are 1, out must be 1.
    check_out_one_when_both_one: assert property (
        @(posedge clk) (a === 1'b1 && b === 1'b1) |-> (out === 1'b1)
    );

    // When any input is 0, out must be 0.
    check_out_zero_when_any_zero: assert property (
        @(posedge clk) ((a === 1'b0) || (b === 1'b0)) |-> (out === 1'b0)
    );

    // Out can be 1 only if both inputs are 1.
    check_out_one_implies_inputs_one: assert property (
        @(posedge clk) (out === 1'b1) |-> (a === 1'b1 && b === 1'b1)
    );

    // If both inputs are stable, output is stable.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> $stable(out)
    );

    // Output changes only when at least one input changes.
    check_out_change_implies_input_change: assert property (
        @(posedge clk) $changed(out) |-> ($changed(a) || $changed(b))
    );

    // Rising edge on out only when both inputs are high.
    check_out_rise_requires_both_high: assert property (
        @(posedge clk) $rose(out) |-> (a === 1'b1 && b === 1'b1)
    );

    // Falling edge on out only when any input is low.
    check_out_fall_requires_any_low: assert property (
        @(posedge clk) $fell(out) |-> ((a === 1'b0) || (b === 1'b0))
    );

    // With known inputs, out is known and equals a & b.
    check_out_known_when_inputs_known: assert property (
        @(posedge clk) ((a inside {1'b0,1'b1}) && (b inside {1'b0,1'b1})) |-> ((out inside {1'b0,1'b1}) && (out === (a & b)))
    );

    // Unknown out implies at least one input is unknown.
    check_x_out_implies_x_input: assert property (
        @(posedge clk) (!(out inside {1'b0,1'b1})) |-> ( !(a inside {1'b0,1'b1}) || !(b inside {1'b0,1'b1}) )
    );
endmodule