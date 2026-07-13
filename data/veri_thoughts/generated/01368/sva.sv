module and_module_sva (
    input logic CLK,   // sampling clock for assertions
    input logic a,
    input logic b,
    input logic out
);
    // Output equals logical AND of inputs.
    check_out_equals_and: assert property (
        @(posedge CLK) out == (a & b)
    );

    // If any input is LOW, output must be LOW.
    check_any_input_low_forces_out_low: assert property (
        @(posedge CLK) (!a || !b) |-> (out == 1'b0)
    );

    // Output change must be caused by a change on at least one input.
    check_out_change_requires_input_change: assert property (
        @(posedge CLK) $changed(out) |-> ($changed(a) || $changed(b))
    );

    // Rising output implies at least one input rose and both are HIGH now.
    check_out_rise_cause: assert property (
        @(posedge CLK) $rose(out) |-> (($rose(a) && b) || ($rose(b) && a))
    );

    // Falling output implies at least one input fell.
    check_out_fall_cause: assert property (
        @(posedge CLK) $fell(out) |-> ($fell(a) || $fell(b))
    );
endmodule