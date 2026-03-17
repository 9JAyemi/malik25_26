module pipelined_circuit_sva(
    input logic [3:0] in,
    input logic out_and,
    input logic out_or,
    input logic out_xor
);

    // out_and is the AND of the two pairwise input AND terms.
    check_out_and_function: assert property (
        @($global_clock)
        out_and == ((in[0] & in[1]) & (in[2] & in[3]))
    );

    // out_or matches the second-stage OR expression.
    check_out_or_stage_function: assert property (
        @($global_clock)
        out_or == (((in[0] & in[1]) | (in[2] & in[3])) | ((in[0] & in[1]) ^ (in[2] & in[3])))
    );

    // out_xor matches the second-stage XOR expression.
    check_out_xor_stage_function: assert property (
        @($global_clock)
        out_xor == (((in[0] & in[1]) | (in[2] & in[3])) ^ ((in[0] & in[1]) ^ (in[2] & in[3])))
    );

    // out_or simplifies to the OR of the two pairwise input AND terms.
    check_out_or_simplified_function: assert property (
        @($global_clock)
        out_or == ((in[0] & in[1]) | (in[2] & in[3]))
    );

    // out_xor is always equal to out_and for this logic.
    check_out_xor_matches_out_and: assert property (
        @($global_clock)
        out_xor == out_and
    );

    // If neither input pair ANDs high, all outputs are low.
    check_no_pair_and_gives_zero_outputs: assert property (
        @($global_clock)
        (!(in[0] & in[1]) && !(in[2] & in[3])) |-> ((out_and == 1'b0) && (out_or == 1'b0) && (out_xor == 1'b0))
    );

    // If exactly one input pair ANDs high, only out_or is high.
    check_one_pair_and_gives_only_or: assert property (
        @($global_clock)
        ((in[0] & in[1]) ^ (in[2] & in[3])) |-> ((out_and == 1'b0) && (out_or == 1'b1) && (out_xor == 1'b0))
    );

    // If both input pairs AND high, all outputs are high.
    check_both_pair_ands_give_all_outputs_high: assert property (
        @($global_clock)
        ((in[0] & in[1]) && (in[2] & in[3])) |-> ((out_and == 1'b1) && (out_or == 1'b1) && (out_xor == 1'b1))
    );

endmodule