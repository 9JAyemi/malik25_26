module mux2to1_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic sel,
    input logic out
);
    // Mux function: out equals sel ? in1 : in0.
    check_mux_function: assert property (
        @(posedge clk) out === (sel ? in1 : in0)
    );

    // When sel is 0, out equals in0.
    check_sel0_path: assert property (
        @(posedge clk) (!sel) |-> (out === in0)
    );

    // When sel is 1, out equals in1.
    check_sel1_path: assert property (
        @(posedge clk) (sel) |-> (out === in1)
    );

    // If sel, in0, and in1 are stable, out is stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(sel) && $stable(in0) && $stable(in1)) |-> $stable(out)
    );

    // If sel stays 0 and in0 changes, out follows in0.
    check_out_follows_in0_when_sel0: assert property (
        @(posedge clk) (!sel && $stable(sel) && $changed(in0)) |-> (out === in0)
    );

    // If sel stays 1 and in1 changes, out follows in1.
    check_out_follows_in1_when_sel1: assert property (
        @(posedge clk) (sel && $stable(sel) && $changed(in1)) |-> (out === in1)
    );

    // If sel stays 0, changes on in1 do not affect out.
    check_unselected_in1_no_effect_when_sel0: assert property (
        @(posedge clk) (!sel && $stable(sel) && $changed(in1)) |-> (out === in0)
    );

    // If sel stays 1, changes on in0 do not affect out.
    check_unselected_in0_no_effect_when_sel1: assert property (
        @(posedge clk) (sel && $stable(sel) && $changed(in0)) |-> (out === in1)
    );

    // Any change on out is caused by a change on sel or the selected input.
    check_out_change_caused_by_inputs: assert property (
        @(posedge clk) $changed(out) |-> ($changed(sel) || ((!sel && $changed(in0)) || (sel && $changed(in1))))
    );

    // If in0 equals in1, out equals that common value regardless of sel.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (in0 === in1) |-> (out === in0)
    );
endmodule