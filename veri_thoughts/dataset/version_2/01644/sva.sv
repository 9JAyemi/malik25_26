module mux4_1_sva (
    input logic CLK,
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic out
);
    ///// Functional mapping /////
    // When sel==00, out equals in[0].
    check_sel_00_routes_in0: assert property (
        @(posedge CLK) disable iff (1'b0) (sel == 2'b00) |-> (out == in[0])
    );
    // When sel==01, out equals in[1].
    check_sel_01_routes_in1: assert property (
        @(posedge CLK) disable iff (1'b0) (sel == 2'b01) |-> (out == in[1])
    );
    // When sel==10, out equals in[2].
    check_sel_10_routes_in2: assert property (
        @(posedge CLK) disable iff (1'b0) (sel == 2'b10) |-> (out == in[2])
    );
    // When sel==11, out equals in[3].
    check_sel_11_routes_in3: assert property (
        @(posedge CLK) disable iff (1'b0) (sel == 2'b11) |-> (out == in[3])
    );
    // Out equals the bit of 'in' indexed by 'sel' at all times.
    check_out_matches_dynamic_index: assert property (
        @(posedge CLK) disable iff (1'b0) (out == in[sel])
    );

    ///// Stability and change behavior /////
    // If inputs 'in' and 'sel' are stable, 'out' remains stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0) ($stable(in) && $stable(sel)) |-> $stable(out)
    );
    // If 'sel' and the selected input bit are stable, 'out' is stable.
    check_no_spurious_change_with_sel_and_selected_input_stable: assert property (
        @(posedge CLK) disable iff (1'b0) ($stable(sel) && $stable(in[sel])) |-> $stable(out)
    );
    // If 'sel' is stable and the selected input bit changes, 'out' changes.
    check_out_changes_when_selected_input_changes: assert property (
        @(posedge CLK) disable iff (1'b0) ($stable(sel) && !$stable(in[sel])) |-> !$stable(out)
    );
    // If 'sel' is stable and 'out' changes, the selected input bit changed.
    check_selected_input_change_needed_for_out_change: assert property (
        @(posedge CLK) disable iff (1'b0) ($stable(sel) && !$stable(out)) |-> !$stable(in[sel])
    );
endmodule