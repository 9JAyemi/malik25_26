module ab_mux_sva (
    input logic CLK,
    input logic a,
    input logic b,
    input logic q
);
    ///// Functional correctness /////
    // q equals logical OR of a and b.
    check_q_is_or: assert property (
        @(posedge CLK) q == (a | b)
    );

    // When both inputs are 0, q must be 0.
    check_zero_zero_results_zero: assert property (
        @(posedge CLK) (a == 1'b0 && b == 1'b0) |-> (q == 1'b0)
    );

    // When a is 0, q must equal b.
    check_a_zero_drives_b: assert property (
        @(posedge CLK) (a == 1'b0) |-> (q == b)
    );

    // When a is 1, q must be 1.
    check_a_one_forces_one: assert property (
        @(posedge CLK) (a == 1'b1) |-> (q == 1'b1)
    );

    // When a is 0 and b is 1, q must be 1.
    check_b_one_when_a_zero: assert property (
        @(posedge CLK) (a == 1'b0 && b == 1'b1) |-> (q == 1'b1)
    );

    // If q is 1, then at least one input must be 1.
    check_q_one_implies_input_one: assert property (
        @(posedge CLK) (q == 1'b1) |-> (a == 1'b1 || b == 1'b1)
    );

    // If q is 0, both inputs must be 0.
    check_q_zero_implies_both_zero: assert property (
        @(posedge CLK) (q == 1'b0) |-> (a == 1'b0 && b == 1'b0)
    );

    ///// Combinational stability /////
    // If inputs hold their values, q must hold its value.
    check_stability_when_inputs_hold: assert property (
        @(posedge CLK) (a == $past(a) && b == $past(b)) |-> (q == $past(q))
    );

    // q only changes when at least one input changes.
    check_q_changes_only_on_input_change: assert property (
        @(posedge CLK) $changed(q) |-> ($changed(a) || $changed(b))
    );

    // When a equals b, q must equal that common value.
    check_when_inputs_equal: assert property (
        @(posedge CLK) (a == b) |-> (q == a)
    );
endmodule