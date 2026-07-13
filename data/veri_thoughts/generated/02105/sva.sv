module sky130_fd_sc_ms__bufinv_sva (
    input  logic CLK,
    input  logic A,
    input  logic Y
);
    // Output is the exact bitwise inversion of input.
    check_function_exact_inversion: assert property (
        @(posedge CLK) disable iff (1'b0) (Y === ~A)
    );

    // Known input implies known output.
    check_known_input_implies_known_output: assert property (
        @(posedge CLK) disable iff (1'b0) (!$isunknown(A)) |-> (!$isunknown(Y))
    );

    // Unknown input propagates to unknown output.
    check_x_propagation_from_input_to_output: assert property (
        @(posedge CLK) disable iff (1'b0) ($isunknown(A)) |-> ($isunknown(Y))
    );

    // When both are known, A and Y must differ.
    check_when_known_they_differ: assert property (
        @(posedge CLK) disable iff (1'b0) ((!$isunknown(A)) && (!$isunknown(Y))) |-> (A !== Y)
    );

    // A rising edge causes Y to fall (inversion relation across cycles).
    check_input_rise_causes_output_fall: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(A) |-> $fell(Y)
    );

    // A falling edge causes Y to rise (inversion relation across cycles).
    check_input_fall_causes_output_rise: assert property (
        @(posedge CLK) disable iff (1'b0) $fell(A) |-> $rose(Y)
    );

    // If input changes between cycles, output also changes.
    check_input_change_causes_output_change: assert property (
        @(posedge CLK) disable iff (1'b0) $changed(A) |-> $changed(Y)
    );

    // If output changes between cycles, input also changes.
    check_output_change_implies_input_change: assert property (
        @(posedge CLK) disable iff (1'b0) $changed(Y) |-> $changed(A)
    );

    // If input is stable between cycles, output is stable.
    check_stable_input_keeps_output_stable: assert property (
        @(posedge CLK) disable iff (1'b0) $stable(A) |-> $stable(Y)
    );

    // Output is never driven to high-Z.
    check_output_never_highz: assert property (
        @(posedge CLK) disable iff (1'b0) (Y !== 1'bz)
    );
endmodule