module mux2to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic sel,
    input logic out,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // When sel is low, out passes A.
    check_selects_a_when_sel_low: assert property (
        @(posedge clk) (sel === 1'b0) |-> (out === A)
    );

    // When sel is high, out passes B.
    check_selects_b_when_sel_high: assert property (
        @(posedge clk) (sel === 1'b1) |-> (out === B)
    );

    // A rising sel switches the output to B.
    check_sel_rise_switches_to_b: assert property (
        @(posedge clk) $rose(sel) |-> (out === B)
    );

    // A falling sel switches the output to A.
    check_sel_fall_switches_to_a: assert property (
        @(posedge clk) $fell(sel) |-> (out === A)
    );

    // A change on unselected B does not affect out when sel stays low.
    check_unselected_b_has_no_effect: assert property (
        @(posedge clk) (sel === 1'b0 && $stable(sel) && $stable(A) && $changed(B)) |-> $stable(out)
    );

    // A change on unselected A does not affect out when sel stays high.
    check_unselected_a_has_no_effect: assert property (
        @(posedge clk) (sel === 1'b1 && $stable(sel) && $stable(B) && $changed(A)) |-> $stable(out)
    );

    // A change on selected A is reflected at out when sel stays low.
    check_selected_a_change_reaches_out: assert property (
        @(posedge clk) (sel === 1'b0 && $stable(sel) && $changed(A)) |-> $changed(out)
    );

    // A change on selected B is reflected at out when sel stays high.
    check_selected_b_change_reaches_out: assert property (
        @(posedge clk) (sel === 1'b1 && $stable(sel) && $changed(B)) |-> $changed(out)
    );

    // Stable mux inputs keep the output stable.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk) $stable({A, B, sel}) |-> $stable(out)
    );

    // Supply-pin changes alone do not affect the RTL output.
    check_supply_pins_do_not_affect_output: assert property (
        @(posedge clk) ($stable({A, B, sel}) && $changed({VPB, VPWR, VGND, VNB})) |-> $stable(out)
    );

endmodule