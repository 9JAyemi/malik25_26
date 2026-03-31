module top_module_sva (
    input logic [15:0] in,
    input logic        out,
    input logic [7:0]  out1,
    input logic [7:0]  out2
);

    // out1 is the low 8 bits of in.
    check_out1_matches_low_byte: assert property (
        @($global_clock) out1 == in[7:0]
    );

    // out2 is the high 8 bits of in.
    check_out2_matches_high_byte: assert property (
        @($global_clock) out2 == in[15:8]
    );

    // out is the AND of out2[0] and out1[0].
    check_out_matches_and_gate: assert property (
        @($global_clock) out == (out2[0] & out1[0])
    );

    // out is high only when both AND inputs are high.
    check_out_high_requires_both_inputs_high: assert property (
        @($global_clock) out |-> (out2[0] && out1[0])
    );

    // Both AND inputs low forces out low.
    check_out_low_when_both_inputs_low: assert property (
        @($global_clock) (!out2[0] || !out1[0]) |-> !out
    );

endmodule