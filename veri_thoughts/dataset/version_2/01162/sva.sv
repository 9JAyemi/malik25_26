module pg_51_sva (
    input logic CLK,
    input logic RESETn,
    input logic g,
    input logic p,
    input logic g_prec,
    input logic p_prec,
    input logic p_out,
    input logic g_out_BAR
);
    // No clock/reset in RTL; combinational only. Sample on CLK; disable during !RESETn.
    // Function: p_out = p & p_prec; g_out_BAR = ~(g_prec & p & g).

    // p_out must be HIGH only when both p and p_prec are HIGH.
    check_p_out_implies_inputs_high: assert property (
        @(posedge CLK) disable iff (!RESETn) p_out |-> (p && p_prec)
    );

    // When both p and p_prec are HIGH, p_out must be HIGH.
    check_inputs_high_imply_p_out: assert property (
        @(posedge CLK) disable iff (!RESETn) (p && p_prec) |-> p_out
    );

    // g_out_BAR must be LOW only when g_prec, p, and g are all HIGH.
    check_g_out_bar_low_implies_all_high: assert property (
        @(posedge CLK) disable iff (!RESETn) !g_out_BAR |-> (g_prec && p && g)
    );

    // When g_prec, p, and g are all HIGH, g_out_BAR must be LOW.
    check_all_high_imply_g_out_bar_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (g_prec && p && g) |-> !g_out_BAR
    );

    // When any of g_prec, p, or g is LOW, g_out_BAR must be HIGH.
    check_any_low_imply_g_out_bar_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (!g_prec || !p || !g) |-> g_out_BAR
    );

    // When either p or p_prec is LOW, p_out must be LOW.
    check_any_low_imply_p_out_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (!p || !p_prec) |-> !p_out
    );

    // If p and p_prec are unchanged, p_out must be unchanged.
    check_p_out_stability_with_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn) !$changed({p, p_prec}) |-> !$changed(p_out)
    );

    // If g, p, and g_prec are unchanged, g_out_BAR must be unchanged.
    check_g_out_bar_stability_with_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn) !$changed({g, p, g_prec}) |-> !$changed(g_out_BAR)
    );

    // A change on p_out must be caused by a change on p or p_prec.
    check_p_out_change_has_cause: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(p_out) |-> $changed({p, p_prec})
    );

    // A change on g_out_BAR must be caused by a change on g, p, or g_prec.
    check_g_out_bar_change_has_cause: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(g_out_BAR) |-> $changed({g, p, g_prec})
    );

endmodule