module bitwise_operations_sva(
    input logic [3:0] in_1,
    input logic [3:0] in_2,
    input logic [3:0] in_3,
    input logic [3:0] in_4,
    input logic out_and,
    input logic out_or,
    input logic out_xor
);

    // No explicit clock or reset exists in the RTL; sample on the formal global clock.
    // The logic is purely combinational, and each scalar output is the bit-0 result of its 4-bit expression.

    // out_and matches the LSB of the cascaded AND computation.
    check_out_and_matches_lsb_and: assert property (
        @($global_clock) out_and === ((in_1[0] & in_2[0]) & (in_3[0] & in_4[0]))
    );

    // out_or matches the LSB of the cascaded OR computation.
    check_out_or_matches_lsb_or: assert property (
        @($global_clock) out_or === ((in_1[0] | in_2[0]) | (in_3[0] | in_4[0]))
    );

    // out_xor matches the LSB of the cascaded XOR computation.
    check_out_xor_matches_lsb_xor: assert property (
        @($global_clock) out_xor === ((in_1[0] ^ in_2[0]) ^ (in_3[0] ^ in_4[0]))
    );

    // out_and changes only when one of the input LSBs changes.
    check_out_and_only_changes_with_lsb_inputs: assert property (
        @($global_clock) $stable({in_1[0], in_2[0], in_3[0], in_4[0]}) |-> $stable(out_and)
    );

    // out_or changes only when one of the input LSBs changes.
    check_out_or_only_changes_with_lsb_inputs: assert property (
        @($global_clock) $stable({in_1[0], in_2[0], in_3[0], in_4[0]}) |-> $stable(out_or)
    );

    // out_xor changes only when one of the input LSBs changes.
    check_out_xor_only_changes_with_lsb_inputs: assert property (
        @($global_clock) $stable({in_1[0], in_2[0], in_3[0], in_4[0]}) |-> $stable(out_xor)
    );

endmodule