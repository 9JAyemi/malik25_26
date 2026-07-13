module sparc_ifu_par34_sva (
    input logic        out,
    input logic [33:0] in
);

    // Output matches the reduction XOR of the 34-bit input.
    check_out_is_reduction_xor: assert property (
        @($global_clock) out === (^in[33:0])
    );

    // A zero input vector has even parity.
    check_zero_vector_even_parity: assert property (
        @($global_clock) (in === 34'b0) |-> (out === 1'b0)
    );

    // An all-ones input vector has even parity over 34 bits.
    check_all_ones_even_parity: assert property (
        @($global_clock) (in === {34{1'b1}}) |-> (out === 1'b0)
    );

    // Any one-hot input vector has odd parity.
    check_onehot_has_odd_parity: assert property (
        @($global_clock) $onehot(in) |-> (out === 1'b1)
    );

    // Any vector with exactly one zero bit has odd parity.
    check_single_zero_has_odd_parity: assert property (
        @($global_clock) $onehot(~in) |-> (out === 1'b1)
    );

    // If the input vector is stable, the output remains stable.
    check_stable_input_stable_output: assert property (
        @($global_clock) $stable(in) |-> $stable(out)
    );

endmodule