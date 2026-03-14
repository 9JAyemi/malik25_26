module and_or_gate_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic y
);
    // Combinational DUT with no reset; use posedge of c as the sampling clock.

    // y equals a & b for all input combinations.
    check_y_eq_and: assert property (
        @(posedge c) (y == (a & b))
    );

    // y high only when both a and b are high.
    check_y_high_implies_inputs_high: assert property (
        @(posedge c) y |-> (a && b)
    );

    // a low forces y low.
    check_a_low_forces_y_low: assert property (
        @(posedge c) (!a) |-> (y == 1'b0)
    );

    // b low forces y low.
    check_b_low_forces_y_low: assert property (
        @(posedge c) (!b) |-> (y == 1'b0)
    );

    // Both inputs high force y high.
    check_both_high_forces_y_high: assert property (
        @(posedge c) (a && b) |-> (y == 1'b1)
    );

    // If a and b are stable across a c edge, y is stable (independent of c).
    check_independence_from_c: assert property (
        @(posedge c) ($stable(a) && $stable(b)) |-> $stable(y)
    );

    // When b is 1, y equals a.
    check_b_one_implies_y_eq_a: assert property (
        @(posedge c) (b == 1'b1) |-> (y == a)
    );

    // When a is 1, y equals b.
    check_a_one_implies_y_eq_b: assert property (
        @(posedge c) (a == 1'b1) |-> (y == b)
    );

    // y rising requires both inputs high.
    check_y_rise_requires_inputs_high: assert property (
        @(posedge c) $rose(y) |-> (a && b)
    );

    // y falling requires at least one input low.
    check_y_fall_requires_input_low: assert property (
        @(posedge c) $fell(y) |-> (!a || !b)
    );
endmodule