module g_18_sva (
    input logic CLK,
    input logic g,
    input logic p,
    input logic [1:0] g_prec,
    input logic g_out
);
    // g_out equals p & g_prec[1] & ~g.
    check_functional_equivalence: assert property (
        @(posedge CLK) g_out == (p & g_prec[1] & ~g)
    );

    // If g_out is 1 then p must be 1.
    check_g_out_implies_p: assert property (
        @(posedge CLK) g_out |-> p
    );

    // If g_out is 1 then g_prec[1] must be 1.
    check_g_out_implies_gprec1: assert property (
        @(posedge CLK) g_out |-> g_prec[1]
    );

    // If g_out is 1 then g must be 0.
    check_g_out_implies_not_g: assert property (
        @(posedge CLK) g_out |-> !g
    );

    // When p=1, g_prec[1]=1, and g=0, g_out must be 1.
    check_one_if_all_true: assert property (
        @(posedge CLK) (p && g_prec[1] && !g) |-> (g_out == 1'b1)
    );

    // g_out is independent of g_prec[0] when other inputs are stable.
    check_independence_gprec0: assert property (
        @(posedge CLK) ($changed(g_prec[0]) && $stable({p, g_prec[1], g})) |-> $stable(g_out)
    );

    // If p, g_prec[1], and g are stable, g_out is stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({p, g_prec[1], g}) |-> $stable(g_out)
    );

    // On p rising with g_prec[1]=1 and g=0, g_out is 1.
    check_g_out_on_p_rise: assert property (
        @(posedge CLK) ($rose(p) && g_prec[1] && !g) |-> (g_out == 1'b1)
    );

    // On g_prec[1] rising with p=1 and g=0, g_out is 1.
    check_g_out_on_gprec1_rise: assert property (
        @(posedge CLK) ($rose(g_prec[1]) && p && !g) |-> (g_out == 1'b1)
    );

    // On g rising with p=1 and g_prec[1]=1, g_out is 0.
    check_g_out_on_g_rise: assert property (
        @(posedge CLK) ($rose(g) && p && g_prec[1]) |-> (g_out == 1'b0)
    );

    // On g falling with p=1 and g_prec[1]=1, g_out is 1.
    check_g_out_on_g_fall: assert property (
        @(posedge CLK) ($fell(g) && p && g_prec[1]) |-> (g_out == 1'b1)
    );

    // On g_prec[1] falling, g_out is 0.
    check_g_out_on_gprec1_fall: assert property (
        @(posedge CLK) $fell(g_prec[1]) |-> (g_out == 1'b0)
    );
endmodule