module MUXn_2_1_sva #(
    parameter int MuxLen = 63
) (
    input logic clk,
    input logic [MuxLen:0] mux_in0,
    input logic [MuxLen:0] mux_in1,
    input logic mux_sel,
    input logic [MuxLen:0] mux_out
);

    // Combinational DUT sampled on clk; no reset is present in the RTL.

    // When select is high, the output must match input 1.
    check_select_high_routes_in1: assert property (
        @(posedge clk) (mux_sel === 1'b1) |-> (mux_out === mux_in1)
    );

    // When select is anything other than high, the output must match input 0.
    check_select_not_high_routes_in0: assert property (
        @(posedge clk) (mux_sel !== 1'b1) |-> (mux_out === mux_in0)
    );

    // The output must always match one of the two inputs.
    check_output_matches_one_input: assert property (
        @(posedge clk) (mux_out === mux_in0) || (mux_out === mux_in1)
    );

    // A change on unselected input 0 must not affect the output when input 1 is selected.
    check_unselected_in0_change_ignored: assert property (
        @(posedge clk)
        (mux_sel === 1'b1 && $stable(mux_sel) && $stable(mux_in1) && $changed(mux_in0))
        |-> $stable(mux_out)
    );

    // A change on unselected input 1 must not affect the output when input 0 is selected.
    check_unselected_in1_change_ignored: assert property (
        @(posedge clk)
        (mux_sel !== 1'b1 && $stable(mux_sel) && $stable(mux_in0) && $changed(mux_in1))
        |-> $stable(mux_out)
    );

    // If both inputs and select are stable, the output must stay stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({mux_in0, mux_in1, mux_sel}) |-> $stable(mux_out)
    );

endmodule