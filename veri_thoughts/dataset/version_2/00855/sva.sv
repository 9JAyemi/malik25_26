module mux_16bit_sva (
    input logic clk,
    input logic [15:0] a,
    input logic [15:0] b,
    input logic sel,
    input logic [15:0] out
);
    // When sel==0, out must equal a.
    check_sel0_routes_a: assert property (
        @(posedge clk) (sel == 1'b0) |-> (out == a)
    );

    // When sel==1, out must equal b.
    check_sel1_routes_b: assert property (
        @(posedge clk) (sel == 1'b1) |-> (out == b)
    );

    // If a and b are equal, out must equal that value regardless of sel.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (a == b) |-> (out == a)
    );

    // With sel==0 held stable and a stable, out remains stable.
    check_out_stable_when_sel0_and_a_stable: assert property (
        @(posedge clk) (sel == 1'b0) && $stable(sel) && $stable(a) |-> $stable(out)
    );

    // With sel==1 held stable and b stable, out remains stable.
    check_out_stable_when_sel1_and_b_stable: assert property (
        @(posedge clk) (sel == 1'b1) && $stable(sel) && $stable(b) |-> $stable(out)
    );

    // With sel==0 held stable, any change on a must change out.
    check_out_follows_a_when_sel0_and_a_changes: assert property (
        @(posedge clk) (sel == 1'b0) && $stable(sel) && $changed(a) |-> $changed(out)
    );

    // With sel==1 held stable, any change on b must change out.
    check_out_follows_b_when_sel1_and_b_changes: assert property (
        @(posedge clk) (sel == 1'b1) && $stable(sel) && $changed(b) |-> $changed(out)
    );

    // If sel toggles while a and b are stable and differ, out must change.
    check_out_changes_on_sel_toggle_when_inputs_differ: assert property (
        @(posedge clk) $changed(sel) && $stable(a) && $stable(b) && (a != b) |-> $changed(out)
    );

    // With sel==0 held stable and a stable, changes on b must not affect out.
    check_unselected_b_change_no_effect_when_sel0: assert property (
        @(posedge clk) (sel == 1'b0) && $stable(sel) && $stable(a) && $changed(b) |-> $stable(out)
    );

    // With sel==1 held stable and b stable, changes on a must not affect out.
    check_unselected_a_change_no_effect_when_sel1: assert property (
        @(posedge clk) (sel == 1'b1) && $stable(sel) && $stable(b) && $changed(a) |-> $stable(out)
    );
endmodule