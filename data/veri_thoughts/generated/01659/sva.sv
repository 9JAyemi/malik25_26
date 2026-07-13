module g_3_sva (
    input logic CLK,
    input logic RESETn,
    input logic g,
    input logic p,
    input logic g_prec,
    input logic g_out
);
    ///// Functional equivalence /////
    // g_out implements g | (g_prec & p).
    check_functional_equivalence: assert property (
        @(posedge CLK) disable iff (!RESETn) (g_out == (g | (g_prec & p)))
    );

    ///// Basic implications /////
    // If g is 1, g_out must be 1.
    check_g_high_forces_one: assert property (
        @(posedge CLK) disable iff (!RESETn) (g == 1'b1) |-> (g_out == 1'b1)
    );
    // If g_prec and p are both 1, g_out must be 1.
    check_gprec_and_p_high_implies_one: assert property (
        @(posedge CLK) disable iff (!RESETn) ((g_prec == 1'b1) && (p == 1'b1)) |-> (g_out == 1'b1)
    );

    ///// Pass-through conditions /////
    // When p is 0, g_out equals g.
    check_p_zero_pass_g: assert property (
        @(posedge CLK) disable iff (!RESETn) (p == 1'b0) |-> (g_out == g)
    );
    // When g_prec is 0, g_out equals g.
    check_gprec_zero_pass_g: assert property (
        @(posedge CLK) disable iff (!RESETn) (g_prec == 1'b0) |-> (g_out == g)
    );
    // When p is 1, g_out equals g | g_prec.
    check_p_one_or_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) (p == 1'b1) |-> (g_out == (g | g_prec))
    );

    ///// Zero-output conditions /////
    // If g and p are 0, g_out must be 0.
    check_g_zero_p_zero_out_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) ((g == 1'b0) && (p == 1'b0)) |-> (g_out == 1'b0)
    );
    // If g and g_prec are 0, g_out must be 0.
    check_g_zero_gprec_zero_out_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) ((g == 1'b0) && (g_prec == 1'b0)) |-> (g_out == 1'b0)
    );

    ///// Conditional passthroughs /////
    // If g is 0 and g_prec is 1, g_out equals p.
    check_g_zero_gprec_one_pass_p: assert property (
        @(posedge CLK) disable iff (!RESETn) ((g == 1'b0) && (g_prec == 1'b1)) |-> (g_out == p)
    );
    // If g is 0 and p is 1, g_out equals g_prec.
    check_g_zero_p_one_pass_gprec: assert property (
        @(posedge CLK) disable iff (!RESETn) ((g == 1'b0) && (p == 1'b1)) |-> (g_out == g_prec)
    );
endmodule