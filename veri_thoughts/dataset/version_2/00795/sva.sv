module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out_always_ff
);
    ///// Functional correctness (registered XNOR of inputs) /////
    // Next cycle output equals XNOR of current inputs.
    check_out_is_xnor_of_inputs_next: assert property (
        @(posedge clk) 1'b1 |-> ##1 (out_always_ff == (a ~^ b))
    );

    // If inputs are equal now, next cycle output is 1.
    check_equal_inputs_imply_out1_next: assert property (
        @(posedge clk) (a == b) |-> ##1 (out_always_ff == 1'b1)
    );

    // If inputs differ now, next cycle output is 0.
    check_unequal_inputs_imply_out0_next: assert property (
        @(posedge clk) (a != b) |-> ##1 (out_always_ff == 1'b0)
    );

    // Alternative XNOR form: (~a & ~b) | (a & b) holds next cycle.
    check_xnor_alternative_expression_next: assert property (
        @(posedge clk) 1'b1 |-> ##1 (out_always_ff == ((~a & ~b) | (a & b)))
    );

    ///// Temporal consistency between input changes and output changes /////
    // If neither input changes this cycle, output is stable next cycle.
    check_no_input_change_keeps_output_stable_next: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> ##1 $stable(out_always_ff)
    );

    // If exactly one input changes this cycle, output changes next cycle.
    check_one_input_toggle_causes_output_toggle_next: assert property (
        @(posedge clk) ($onehot({$changed(a), $changed(b)})) |-> ##1 $changed(out_always_ff)
    );

    // If both inputs change this cycle, output is stable next cycle.
    check_both_inputs_toggle_keeps_output_stable_next: assert property (
        @(posedge clk) ($changed(a) && $changed(b)) |-> ##1 $stable(out_always_ff)
    );

    // If only a changes (b stable), output changes next cycle.
    check_a_toggle_only_causes_output_toggle_next: assert property (
        @(posedge clk) ($changed(a) && $stable(b)) |-> ##1 $changed(out_always_ff)
    );

    // If only b changes (a stable), output changes next cycle.
    check_b_toggle_only_causes_output_toggle_next: assert property (
        @(posedge clk) ($changed(b) && $stable(a)) |-> ##1 $changed(out_always_ff)
    );
endmodule