module pg_49_sva (
    input logic clk,
    input logic g,
    input logic p,
    input logic g_prec,
    input logic p_prec,
    input logic p_out,
    input logic g_out_BAR
);

    // p_out implements p AND p_prec.
    check_p_out_and_function: assert property (
        @(posedge clk) p_out == (p & p_prec)
    );

    // g_out_BAR implements NOR of g_prec and p.
    check_g_out_bar_nor_function: assert property (
        @(posedge clk) g_out_BAR == ~(g_prec | p)
    );

    // p_out can only be high when both inputs are high.
    check_p_out_high_requires_inputs_high: assert property (
        @(posedge clk) p_out |-> (p && p_prec)
    );

    // p_out must be low if either input is low.
    check_p_out_low_when_any_input_low: assert property (
        @(posedge clk) (!p || !p_prec) |-> !p_out
    );

    // g_out_BAR can only be high when both NOR inputs are low.
    check_g_out_bar_high_requires_inputs_low: assert property (
        @(posedge clk) g_out_BAR |-> (!g_prec && !p)
    );

    // g_out_BAR must be low if either NOR input is high.
    check_g_out_bar_low_when_any_input_high: assert property (
        @(posedge clk) (g_prec || p) |-> !g_out_BAR
    );

    // A high p_out forces g_out_BAR low because p must be high.
    check_p_out_implies_g_out_bar_low: assert property (
        @(posedge clk) p_out |-> !g_out_BAR
    );

    // Changing only g does not affect either output.
    check_g_unused_in_output_logic: assert property (
        @(posedge clk) $changed(g) && $stable({p, g_prec, p_prec}) |-> $stable({p_out, g_out_BAR})
    );

    // Stable AND inputs keep p_out stable.
    check_p_out_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({p, p_prec}) |-> $stable(p_out)
    );

    // Stable NOR inputs keep g_out_BAR stable.
    check_g_out_bar_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({g_prec, p}) |-> $stable(g_out_BAR)
    );

endmodule