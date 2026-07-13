module logic_gate_sva (
    input logic a,
    input logic b,
    input logic g_out,
    input logic p_out
);

    // p_out must be the XOR of a and b.
    check_p_out_is_xor: assert property (
        @($global_clock) p_out == (a ^ b)
    );

    // g_out must be the AND of a and b.
    check_g_out_is_and: assert property (
        @($global_clock) g_out == (a & b)
    );

    // The two outputs can never be high together.
    check_outputs_mutually_exclusive: assert property (
        @($global_clock) !(p_out && g_out)
    );

    // Both low inputs must drive both outputs low.
    check_zero_zero_case: assert property (
        @($global_clock) (!a && !b) |-> (!p_out && !g_out)
    );

    // Different inputs must drive p_out high and g_out low.
    check_inputs_differ_case: assert property (
        @($global_clock) (a ^ b) |-> (p_out && !g_out)
    );

    // Both high inputs must drive g_out high and p_out low.
    check_one_one_case: assert property (
        @($global_clock) (a && b) |-> (g_out && !p_out)
    );

endmodule