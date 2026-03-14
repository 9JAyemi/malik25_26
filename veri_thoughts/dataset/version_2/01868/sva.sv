module pg_45_sva (
    input  logic CLK,
    input  logic g,
    input  logic p,
    input  logic g_prec,
    input  logic p_prec,
    input  logic p_out,
    input  logic g_out_BAR
);
    ///// Combinational equivalence /////
    // p_out equals p_prec AND p.
    check_p_out_equation: assert property (
        @(posedge CLK) p_out == (p_prec & p)
    );
    // g_out_BAR equals NOT((g_prec AND p) OR g).
    check_g_out_BAR_equation: assert property (
        @(posedge CLK) g_out_BAR == ~((g_prec & p) | g)
    );

    ///// Derived implications from logic /////
    // If p is LOW then p_out must be LOW.
    check_p_out_low_if_p_low: assert property (
        @(posedge CLK) (!p) |-> (p_out == 1'b0)
    );
    // If p_prec is LOW then p_out must be LOW.
    check_p_out_low_if_p_prec_low: assert property (
        @(posedge CLK) (!p_prec) |-> (p_out == 1'b0)
    );
    // If both p and p_prec are HIGH then p_out must be HIGH.
    check_p_out_high_if_both_high: assert property (
        @(posedge CLK) (p && p_prec) |-> (p_out == 1'b1)
    );
    // If p_out is HIGH then both p and p_prec are HIGH.
    check_p_out_implies_inputs_high: assert property (
        @(posedge CLK) p_out |-> (p && p_prec)
    );

    // If g is HIGH then g_out_BAR must be LOW.
    check_g_out_bar_low_if_g_high: assert property (
        @(posedge CLK) g |-> (g_out_BAR == 1'b0)
    );
    // If g_prec AND p are HIGH then g_out_BAR must be LOW.
    check_g_out_bar_low_if_gprec_and_p: assert property (
        @(posedge CLK) (g_prec && p) |-> (g_out_BAR == 1'b0)
    );
    // If g is LOW and (g_prec AND p) is LOW then g_out_BAR must be HIGH.
    check_g_out_bar_high_if_both_low: assert property (
        @(posedge CLK) (!g && !(g_prec && p)) |-> (g_out_BAR == 1'b1)
    );
    // If g_out_BAR is HIGH then g is LOW and (g_prec AND p) is LOW.
    check_g_out_bar_high_implies_inputs_low: assert property (
        @(posedge CLK) g_out_BAR |-> (!g && !(g_prec && p))
    );
endmodule