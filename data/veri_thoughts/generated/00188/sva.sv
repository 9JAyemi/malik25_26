module and_gate_sva (
    input logic in1,
    input logic in2,
    input logic out
);

    // The output must always equal the AND of the two inputs.
    check_out_equals_and_of_inputs: assert property (
        @($global_clock) out == (in1 & in2)
    );

    // A low first input must force the output low.
    check_in1_low_forces_out_low: assert property (
        @($global_clock) (in1 == 1'b0) |-> (out == 1'b0)
    );

    // A low second input must force the output low.
    check_in2_low_forces_out_low: assert property (
        @($global_clock) (in2 == 1'b0) |-> (out == 1'b0)
    );

    // Both high inputs must drive the output high.
    check_both_inputs_high_drive_out_high: assert property (
        @($global_clock) ((in1 == 1'b1) && (in2 == 1'b1)) |-> (out == 1'b1)
    );

endmodule