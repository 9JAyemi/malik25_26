module mux_2to1_sva (
    input logic clk,     // sampling clock for SVA (DUT has no clock/reset)
    input logic in0,
    input logic in1,
    input logic sel,
    input logic out
);
    // When sel=1, out equals in1.
    check_sel1_routes_in1: assert property (
        @(posedge clk) sel |-> (out == in1)
    );

    // When sel=0, out equals in0.
    check_sel0_routes_in0: assert property (
        @(posedge clk) !sel |-> (out == in0)
    );

    // If inputs are equal, out equals that value regardless of sel.
    check_equal_inputs_bypass: assert property (
        @(posedge clk) (in0 == in1) |-> (out == in0)
    );

    // If inputs differ and out equals in0, sel must be 0.
    check_out_eq_in0_implies_sel0: assert property (
        @(posedge clk) (in0 != in1) && (out == in0) |-> (!sel)
    );

    // If inputs differ and out equals in1, sel must be 1.
    check_out_eq_in1_implies_sel1: assert property (
        @(posedge clk) (in0 != in1) && (out == in1) |-> (sel)
    );

    // With sel and both inputs stable, out remains stable.
    check_stable_out_when_all_stable: assert property (
        @(posedge clk) $stable(sel) && $stable(in0) && $stable(in1) |-> $stable(out)
    );

    // With sel=1 held stable and in1 stable, out remains stable (in0 may toggle).
    check_unselected_in0_no_effect_when_sel1: assert property (
        @(posedge clk) sel && $stable(sel) && $stable(in1) |-> $stable(out)
    );

    // With sel=0 held stable and in0 stable, out remains stable (in1 may toggle).
    check_unselected_in1_no_effect_when_sel0: assert property (
        @(posedge clk) !sel && $stable(sel) && $stable(in0) |-> $stable(out)
    );
endmodule