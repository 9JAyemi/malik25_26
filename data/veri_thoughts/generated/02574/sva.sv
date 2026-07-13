module AND_GATE_sva (
    input logic a,
    input logic b,
    input logic y
);

    // y equals a & b when a rises.
    check_y_eq_and_on_posedge_a: assert property (
        @(posedge a) y == (a & b)
    );

    // y equals a & b when a falls.
    check_y_eq_and_on_negedge_a: assert property (
        @(negedge a) y == (a & b)
    );

    // y equals a & b when b rises.
    check_y_eq_and_on_posedge_b: assert property (
        @(posedge b) y == (a & b)
    );

    // y equals a & b when b falls.
    check_y_eq_and_on_negedge_b: assert property (
        @(negedge b) y == (a & b)
    );

    // When y rises, both inputs must be 1.
    check_y_rise_requires_inputs_high: assert property (
        @(posedge y) (a && b)
    );

    // When y falls, at least one input must be 0.
    check_y_fall_requires_an_input_low: assert property (
        @(negedge y) (!a || !b)
    );

    // y equals a & b when y rises (redundant functional check on y edge).
    check_y_eq_and_on_posedge_y: assert property (
        @(posedge y) y == (a & b)
    );

    // y equals a & b when y falls (redundant functional check on y edge).
    check_y_eq_and_on_negedge_y: assert property (
        @(negedge y) y == (a & b)
    );

endmodule