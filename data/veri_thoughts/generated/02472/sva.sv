module mux4to1_sva (
    input  logic        CLK,   // external sampling clock for assertions
    input  logic [3:0]  in,
    input  logic [1:0]  sel,
    input  logic        out
);

    // When sel==00, out equals in[0].
    check_sel00_routes_in0: assert property (
        @(posedge CLK) (sel == 2'b00) |-> (out == in[0])
    );

    // When sel==01, out equals in[1].
    check_sel01_routes_in1: assert property (
        @(posedge CLK) (sel == 2'b01) |-> (out == in[1])
    );

    // When sel==10, out equals in[2].
    check_sel10_routes_in2: assert property (
        @(posedge CLK) (sel == 2'b10) |-> (out == in[2])
    );

    // When sel==11, out equals in[3].
    check_sel11_routes_in3: assert property (
        @(posedge CLK) (sel == 2'b11) |-> (out == in[3])
    );

    // With valid, stable sel and stable selected input, out stays stable.
    check_out_stable_when_sel_and_selected_input_stable: assert property (
        @(posedge CLK) (sel inside {2'b00,2'b01,2'b10,2'b11}) && $stable(sel) && $stable(in[sel]) |-> $stable(out)
    );

    // With valid, stable sel, if selected input changes, out changes.
    check_out_changes_with_selected_input_change_when_sel_stable: assert property (
        @(posedge CLK) (sel inside {2'b00,2'b01,2'b10,2'b11}) && $stable(sel) && $changed(in[sel]) |-> $changed(out)
    );

    // Changes on non-selected inputs do not affect out when sel==00 and in[0] is stable.
    check_nonselected_change_no_effect_sel00: assert property (
        @(posedge CLK) (sel == 2'b00) && $stable(in[0]) && ($changed(in[1]) || $changed(in[2]) || $changed(in[3])) |-> $stable(out)
    );

    // Changes on non-selected inputs do not affect out when sel==01 and in[1] is stable.
    check_nonselected_change_no_effect_sel01: assert property (
        @(posedge CLK) (sel == 2'b01) && $stable(in[1]) && ($changed(in[0]) || $changed(in[2]) || $changed(in[3])) |-> $stable(out)
    );

    // Changes on non-selected inputs do not affect out when sel==10 and in[2] is stable.
    check_nonselected_change_no_effect_sel10: assert property (
        @(posedge CLK) (sel == 2'b10) && $stable(in[2]) && ($changed(in[0]) || $changed(in[1]) || $changed(in[3])) |-> $stable(out)
    );

    // Changes on non-selected inputs do not affect out when sel==11 and in[3] is stable.
    check_nonselected_change_no_effect_sel11: assert property (
        @(posedge CLK) (sel == 2'b11) && $stable(in[3]) && ($changed(in[0]) || $changed(in[1]) || $changed(in[2])) |-> $stable(out)
    );

endmodule