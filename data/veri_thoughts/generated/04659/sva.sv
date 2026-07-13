module reduce_and_sva (
    input logic [3:0] in_vec,
    input logic out_bit
);

    // Output must equal the reduction-AND of the input vector.
    check_reduce_and_equation: assert property (
        @($global_clock) out_bit === (&in_vec)
    );

    // All input bits high must drive the output high.
    check_all_inputs_high_drives_output_high: assert property (
        @($global_clock) (in_vec === 4'b1111) |-> (out_bit === 1'b1)
    );

    // A high output requires all input bits to be high.
    check_output_high_requires_all_inputs_high: assert property (
        @($global_clock) (out_bit === 1'b1) |-> (in_vec === 4'b1111)
    );

    // A low bit 0 must force the output low.
    check_bit0_low_forces_output_low: assert property (
        @($global_clock) (in_vec[0] === 1'b0) |-> (out_bit === 1'b0)
    );

    // A low bit 1 must force the output low.
    check_bit1_low_forces_output_low: assert property (
        @($global_clock) (in_vec[1] === 1'b0) |-> (out_bit === 1'b0)
    );

    // A low bit 2 must force the output low.
    check_bit2_low_forces_output_low: assert property (
        @($global_clock) (in_vec[2] === 1'b0) |-> (out_bit === 1'b0)
    );

    // A low bit 3 must force the output low.
    check_bit3_low_forces_output_low: assert property (
        @($global_clock) (in_vec[3] === 1'b0) |-> (out_bit === 1'b0)
    );

endmodule