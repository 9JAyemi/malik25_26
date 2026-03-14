module mux_2to1_sva (
    input logic clk,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic sel,
    input logic [7:0] out
);
    // Out must equal the selected input every cycle.
    mapping_exact: assert property (
        @(posedge clk) out == (sel ? in2 : in1)
    );

    // When sel=0, out equals in1.
    sel0_selects_in1: assert property (
        @(posedge clk) !sel |-> (out == in1)
    );

    // When sel=1, out equals in2.
    sel1_selects_in2: assert property (
        @(posedge clk) sel |-> (out == in2)
    );

    // If in1==in2, out equals that value.
    equal_inputs_imply_out_equal: assert property (
        @(posedge clk) (in1 == in2) |-> (out == in1)
    );

    // When sel=0, changes on in2 do not change out.
    ignore_in2_when_sel0: assert property (
        @(posedge clk) (!sel && $changed(in2)) |-> $stable(out)
    );

    // When sel=1, changes on in1 do not change out.
    ignore_in1_when_sel1: assert property (
        @(posedge clk) (sel && $changed(in1)) |-> $stable(out)
    );

    // If sel and inputs are stable, out is stable.
    stable_inputs_keep_out_stable: assert property (
        @(posedge clk) $stable(sel) && $stable(in1) && $stable(in2) |-> $stable(out)
    );

    // Out changes only if sel or one of the inputs changes.
    out_change_has_cause: assert property (
        @(posedge clk) $changed(out) |-> ($changed(sel) || $changed(in1) || $changed(in2))
    );

    // Out equals one of the two inputs every cycle.
    out_is_one_of_inputs: assert property (
        @(posedge clk) (out == in1) || (out == in2)
    );
endmodule