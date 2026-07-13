module mux_2to1_sva (
    input logic clk,   // Sampling clock for assertions (RTL has no clock/reset)
    input logic in0,
    input logic in1,
    input logic sel,
    input logic out
);
    // Function: out implements a 2:1 mux: out = (in0 & ~sel) | (in1 & sel).
    check_mux_equation: assert property (
        @(posedge clk) out == ((in0 & ~sel) | (in1 & sel))
    );

    // When sel=0, out equals in0.
    check_sel0_path: assert property (
        @(posedge clk) (!sel) |-> (out == in0)
    );

    // When sel=1, out equals in1.
    check_sel1_path: assert property (
        @(posedge clk) (sel) |-> (out == in1)
    );

    // If inputs are equal, out matches that value.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (in0 == in1) |-> (out == in0)
    );

    // With sel held 0 and in0 stable, changes on in1 do not change out.
    check_in1_masked_when_sel0: assert property (
        @(posedge clk) (!sel && $stable(sel) && $stable(in0) && !$stable(in1)) |-> $stable(out)
    );

    // With sel held 1 and in1 stable, changes on in0 do not change out.
    check_in0_masked_when_sel1: assert property (
        @(posedge clk) (sel && $stable(sel) && $stable(in1) && !$stable(in0)) |-> $stable(out)
    );

    // On sel rising edge, out immediately selects in1.
    check_sel_rise_selects_in1: assert property (
        @(posedge clk) $rose(sel) |-> (out == in1)
    );

    // On sel falling edge, out immediately selects in0.
    check_sel_fall_selects_in0: assert property (
        @(posedge clk) $fell(sel) |-> (out == in0)
    );
endmodule