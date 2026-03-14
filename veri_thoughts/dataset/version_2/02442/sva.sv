module top_module_sva (
    input logic clk,
    input logic reset, // synchronous active-high
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [1:0] sel,
    input logic [3:0] q
);

    // When sel==00, q equals a.
    check_sel00_routes_a: assert property (
        @(posedge clk) disable iff (reset) (sel == 2'b00) |-> (q == a)
    );

    // When sel!=00, q equals b.
    check_sel_not00_routes_b: assert property (
        @(posedge clk) disable iff (reset) (sel != 2'b00) |-> (q == b)
    );

    // q is always either a or b.
    check_q_is_a_or_b_only: assert property (
        @(posedge clk) disable iff (reset) (q == a) || (q == b)
    );

    // If inputs differ and q==a, selection must be 00.
    check_q_eq_a_implies_sel00_when_inputs_differ: assert property (
        @(posedge clk) disable iff (reset) ((a != b) && (q == a)) |-> (sel == 2'b00)
    );

    // If inputs differ and q==b, selection must be not 00.
    check_q_eq_b_implies_sel_not00_when_inputs_differ: assert property (
        @(posedge clk) disable iff (reset) ((a != b) && (q == b)) |-> (sel != 2'b00)
    );

    // If a==b, q equals that value regardless of sel.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) disable iff (reset) (a == b) |-> (q == a)
    );

    // With stable a,b,sel across a cycle, q remains stable.
    check_stability_with_stable_inputs: assert property (
        @(posedge clk) disable iff (reset) ($stable(a) && $stable(b) && $stable(sel)) |-> $stable(q)
    );

    // On transition to sel==00 with stable, different inputs, q changes to a.
    check_q_changes_on_sel_to_00: assert property (
        @(posedge clk) disable iff (reset)
            ($rose(sel == 2'b00) && $stable(a) && $stable(b) && (a != b)) |-> ($changed(q) && (q == a))
    );

    // On transition away from sel==00 with stable, different inputs, q changes to b.
    check_q_changes_on_sel_from_00: assert property (
        @(posedge clk) disable iff (reset)
            ($fell(sel == 2'b00) && $stable(a) && $stable(b) && (a != b)) |-> ($changed(q) && (q == b))
    );

    // If sel toggles and a==b with stable inputs, q does not change.
    check_no_q_change_on_sel_toggle_when_inputs_equal: assert property (
        @(posedge clk) disable iff (reset)
            ( ($rose(sel == 2'b00) || $fell(sel == 2'b00)) && $stable(a) && $stable(b) && (a == b) ) |-> !$changed(q)
    );

endmodule