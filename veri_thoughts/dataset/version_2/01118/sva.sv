module sub_sva (
    input logic [125:0] a,
    input logic clk,
    input logic q
);
    // Clock: clk (posedge). No reset present. Combinational function: q = a[125] & a[0].

    // q equals the AND of a[125] and a[0].
    check_q_equals_and: assert property (
        @(posedge clk) q == (a[125] & a[0])
    );

    // If a[125] is 0, q must be 0.
    check_q_low_when_a125_low: assert property (
        @(posedge clk) (a[125] == 1'b0) |-> (q == 1'b0)
    );

    // If a[0] is 0, q must be 0.
    check_q_low_when_a0_low: assert property (
        @(posedge clk) (a[0] == 1'b0) |-> (q == 1'b0)
    );

    // If both inputs are 1, q must be 1.
    check_q_high_when_both_high: assert property (
        @(posedge clk) ((a[125] == 1'b1) && (a[0] == 1'b1)) |-> (q == 1'b1)
    );

    // If q is 1, both inputs must be 1.
    check_inputs_high_when_q_high: assert property (
        @(posedge clk) (q == 1'b1) |-> ((a[125] == 1'b1) && (a[0] == 1'b1))
    );

    // A rising edge on q implies both inputs are 1 now.
    check_q_rise_requires_inputs_high: assert property (
        @(posedge clk) $rose(q) |-> (a[125] == 1'b1) && (a[0] == 1'b1)
    );

    // A falling edge on q implies at least one input is 0 now.
    check_q_fall_requires_any_input_low: assert property (
        @(posedge clk) $fell(q) |-> ((a[125] == 1'b0) || (a[0] == 1'b0))
    );

    // If a[125] and a[0] hold their values, q must be stable.
    check_q_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a[125]) && $stable(a[0])) |-> $stable(q)
    );

    // If a[125] rises and a[0] is 1, q must rise.
    check_q_rise_due_to_a125_rise: assert property (
        @(posedge clk) ($rose(a[125]) && (a[0] == 1'b1)) |-> $rose(q)
    );

    // If a[0] rises and a[125] is 1, q must rise.
    check_q_rise_due_to_a0_rise: assert property (
        @(posedge clk) ($rose(a[0]) && (a[125] == 1'b1)) |-> $rose(q)
    );

endmodule