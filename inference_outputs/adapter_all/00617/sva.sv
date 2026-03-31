module and_or_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic g_out,
    input logic p_out
);

    // g_out must equal the AND of a and b.
    check_g_out_matches_and: assert property (
        @(posedge clk) g_out == (a & b)
    );

    // p_out must equal the OR of a and b.
    check_p_out_matches_or: assert property (
        @(posedge clk) p_out == (a | b)
    );

    // Both inputs low must drive both outputs low.
    check_both_inputs_low_drive_outputs_low: assert property (
        @(posedge clk) (!a && !b) |-> (!g_out && !p_out)
    );

    // Both inputs high must drive both outputs high.
    check_both_inputs_high_drive_outputs_high: assert property (
        @(posedge clk) (a && b) |-> (g_out && p_out)
    );

    // A low and a high input must drive both outputs high.
    check_a_low_b_high_drives_outputs_high: assert property (
        @(posedge clk) (!a && b) |-> (g_out && p_out)
    );

    // A high and a low input must drive both outputs high.
    check_a_high_b_low_drives_outputs_high: assert property (
        @(posedge clk) (a && !b) |-> (g_out && p_out)
    );

    // A high g_out requires both inputs high.
    check_g_out_high_requires_both_inputs_high: assert property (
        @(posedge clk) g_out |-> (a && b)
    );

    // A high p_out requires at least one input high.
    check_p_out_high_requires_any_input_high: assert property (
        @(posedge clk) p_out |-> (a || b)
    );

endmodule