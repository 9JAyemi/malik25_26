module g_17_assertions (
    input logic clk,
    input logic g,
    input logic p,
    input logic g_prec,
    input logic g_out
);

    // g_out matches the implemented three-input AND function.
    check_gout_matches_three_input_and: assert property (
        @(posedge clk) g_out == (g & p & g_prec)
    );

    // A HIGH output requires all three inputs HIGH.
    check_output_high_requires_all_inputs_high: assert property (
        @(posedge clk) (g_out == 1'b1) |-> ((g == 1'b1) && (p == 1'b1) && (g_prec == 1'b1))
    );

    // All three inputs HIGH drive the output HIGH.
    check_all_inputs_high_drive_output_high: assert property (
        @(posedge clk) ((g == 1'b1) && (p == 1'b1) && (g_prec == 1'b1)) |-> (g_out == 1'b1)
    );

    // g LOW forces the output LOW.
    check_g_low_forces_output_low: assert property (
        @(posedge clk) (g == 1'b0) |-> (g_out == 1'b0)
    );

    // p LOW forces the output LOW.
    check_p_low_forces_output_low: assert property (
        @(posedge clk) (p == 1'b0) |-> (g_out == 1'b0)
    );

    // g_prec LOW forces the output LOW.
    check_gprec_low_forces_output_low: assert property (
        @(posedge clk) (g_prec == 1'b0) |-> (g_out == 1'b0)
    );

    // With p and g_prec HIGH, the output tracks g.
    check_output_tracks_g_when_others_high: assert property (
        @(posedge clk) ((p == 1'b1) && (g_prec == 1'b1)) |-> (g_out == g)
    );

    // With g and g_prec HIGH, the output tracks p.
    check_output_tracks_p_when_others_high: assert property (
        @(posedge clk) ((g == 1'b1) && (g_prec == 1'b1)) |-> (g_out == p)
    );

    // With g and p HIGH, the output tracks g_prec.
    check_output_tracks_gprec_when_others_high: assert property (
        @(posedge clk) ((g == 1'b1) && (p == 1'b1)) |-> (g_out == g_prec)
    );

endmodule