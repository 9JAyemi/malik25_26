module top_module_assertions(
    input logic a,
    input logic b,
    input logic out_behavioral,
    input logic out_structural
);

    // Behavioral output is the XOR of the inputs.
    check_behavioral_xor: assert property (
        @($global_clock) out_behavioral == (a ^ b)
    );

    // Structural output simplifies to the value of a.
    check_structural_equals_a: assert property (
        @($global_clock) out_structural == a
    );

    // The two outputs are related by XOR with b.
    check_outputs_related_by_b: assert property (
        @($global_clock) out_behavioral == (out_structural ^ b)
    );

    // When b is low, both outputs match.
    check_outputs_match_when_b_low: assert property (
        @($global_clock) !b |-> (out_behavioral == out_structural)
    );

    // When b is high, the outputs are complements.
    check_outputs_complement_when_b_high: assert property (
        @($global_clock) b |-> (out_behavioral == ~out_structural)
    );

endmodule