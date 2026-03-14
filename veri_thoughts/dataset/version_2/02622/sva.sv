module mux4to1_sva (
    input logic [1:0] sel,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out
);

    // Helper: compute the expected mux output from sel and inputs.
    function automatic logic selected_input_value (
        input logic [1:0] s,
        input logic i0, i1, i2, i3
    );
        case (s)
            2'b00: selected_input_value = i0;
            2'b01: selected_input_value = i1;
            2'b10: selected_input_value = i2;
            default: selected_input_value = i3;
        endcase
    endfunction

    ///// Functional correctness checks /////

    // Output equals selected input when sel[0] rises.
    check_out_matches_sel_on_sel0_posedge: assert property (
        @(posedge sel[0]) out == selected_input_value(sel, in0, in1, in2, in3)
    );

    // Output equals selected input when sel[1] rises.
    check_out_matches_sel_on_sel1_posedge: assert property (
        @(posedge sel[1]) out == selected_input_value(sel, in0, in1, in2, in3)
    );

    // Output equals selected input when in0 rises.
    check_out_matches_sel_on_in0_posedge: assert property (
        @(posedge in0) out == selected_input_value(sel, in0, in1, in2, in3)
    );

    // Output equals selected input when in1 rises.
    check_out_matches_sel_on_in1_posedge: assert property (
        @(posedge in1) out == selected_input_value(sel, in0, in1, in2, in3)
    );

    // Output equals selected input when in2 rises.
    check_out_matches_sel_on_in2_posedge: assert property (
        @(posedge in2) out == selected_input_value(sel, in0, in1, in2, in3)
    );

    // Output equals selected input when in3 rises.
    check_out_matches_sel_on_in3_posedge: assert property (
        @(posedge in3) out == selected_input_value(sel, in0, in1, in2, in3)
    );

    // When sel==00, out mirrors in0 on in0 rising edges.
    check_route_in0_when_sel00: assert property (
        @(posedge in0) (sel == 2'b00) |-> (out == in0)
    );

    // When sel==01, out mirrors in1 on in1 rising edges.
    check_route_in1_when_sel01: assert property (
        @(posedge in1) (sel == 2'b01) |-> (out == in1)
    );

    // When sel==10, out mirrors in2 on in2 rising edges.
    check_route_in2_when_sel10: assert property (
        @(posedge in2) (sel == 2'b10) |-> (out == in2)
    );

    // When sel==11, out mirrors in3 on in3 rising edges.
    check_route_in3_when_sel11: assert property (
        @(posedge in3) (sel == 2'b11) |-> (out == in3)
    );

    // When out rises, it equals the value of the currently selected input.
    check_out_posedge_matches_selected: assert property (
        @(posedge out) out == selected_input_value(sel, in0, in1, in2, in3)
    );

endmodule