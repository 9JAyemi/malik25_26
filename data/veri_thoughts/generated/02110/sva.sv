module mux_2to1_sva (
    input logic CLK,
    input logic RESETn,
    input logic sel,
    input logic in0,
    input logic in1,
    input logic out
);
    // Out equals the combinational ternary function sel ? in1 : in0.
    check_mux_function: assert property (
        @(posedge CLK) disable iff (!RESETn) out === (sel ? in1 : in0)
    );

    // When sel is 0, out equals in0 in the same cycle.
    check_sel0_maps_to_in0: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 1'b0) |-> (out === in0)
    );

    // When sel is 1, out equals in1 in the same cycle.
    check_sel1_maps_to_in1: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 1'b1) |-> (out === in1)
    );

    // With sel=0 and stable, and in0 stable, changes on in1 do not change out.
    check_unselected_in1_no_effect: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 1'b0 && $stable(sel) && $stable(in0) && $changed(in1)) |-> $stable(out)
    );

    // With sel=1 and stable, and in1 stable, changes on in0 do not change out.
    check_unselected_in0_no_effect: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel == 1'b1 && $stable(sel) && $stable(in1) && $changed(in0)) |-> $stable(out)
    );

    // If both inputs are equal and stable, toggling sel keeps out stable.
    check_sel_toggle_equal_inputs_stable_out: assert property (
        @(posedge CLK) disable iff (!RESETn) ($stable(in0) && $stable(in1) && (in0 === in1) && $changed(sel)) |-> $stable(out)
    );

    // If sel, in0, and in1 are all stable, out must be stable.
    check_stable_inputs_keep_out_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) ($stable(sel) && $stable(in0) && $stable(in1)) |-> $stable(out)
    );

    // When in0 equals in1, out equals that value regardless of sel.
    check_equal_inputs_reflect_on_out: assert property (
        @(posedge CLK) disable iff (!RESETn) (in0 === in1) |-> (out === in0)
    );
endmodule