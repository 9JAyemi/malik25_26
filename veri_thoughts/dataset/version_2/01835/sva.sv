module inverted_5input_OR_gate_sva (
    input  logic CLK,
    input  logic p1,
    input  logic p2,
    input  logic p3,
    input  logic p4,
    input  logic p5,
    input  logic y
);
    // Output is 0 when any input is 1.
    check_any_high_forces_y0: assert property (
        @(posedge CLK) disable iff (1'b0)
        ((p1 === 1'b1) || (p2 === 1'b1) || (p3 === 1'b1) || (p4 === 1'b1) || (p5 === 1'b1)) |-> (y === 1'b0)
    );

    // Output is 1 when all inputs are 0.
    check_all_low_forces_y1: assert property (
        @(posedge CLK) disable iff (1'b0)
        ((p1 === 1'b0) && (p2 === 1'b0) && (p3 === 1'b0) && (p4 === 1'b0) && (p5 === 1'b0)) |-> (y === 1'b1)
    );

    // If y is 0, at least one input must be 1.
    check_y0_implies_some_high: assert property (
        @(posedge CLK) disable iff (1'b0)
        (y === 1'b0) |-> ((p1 === 1'b1) || (p2 === 1'b1) || (p3 === 1'b1) || (p4 === 1'b1) || (p5 === 1'b1))
    );

    // If y is 1, no input is 1.
    check_y1_implies_no_high: assert property (
        @(posedge CLK) disable iff (1'b0)
        (y === 1'b1) |-> ((p1 !== 1'b1) && (p2 !== 1'b1) && (p3 !== 1'b1) && (p4 !== 1'b1) && (p5 !== 1'b1))
    );

    // If no input is 1 (including X/Z), output is 1.
    check_no_known_highs_forces_y1: assert property (
        @(posedge CLK) disable iff (1'b0)
        ((p1 !== 1'b1) && (p2 !== 1'b1) && (p3 !== 1'b1) && (p4 !== 1'b1) && (p5 !== 1'b1)) |-> (y === 1'b1)
    );

    // y is always a known 0 or 1.
    check_y_is_binary: assert property (
        @(posedge CLK) disable iff (1'b0)
        (y === 1'b0) || (y === 1'b1)
    );

    // With stable inputs, y must be stable.
    check_stable_inputs_hold_y: assert property (
        @(posedge CLK) disable iff (1'b0)
        $stable({p1,p2,p3,p4,p5}) |-> $stable(y)
    );

    // A falling y requires at least one input to be 1.
    check_y_fall_requires_high: assert property (
        @(posedge CLK) disable iff (1'b0)
        $fell(y) |-> ((p1 === 1'b1) || (p2 === 1'b1) || (p3 === 1'b1) || (p4 === 1'b1) || (p5 === 1'b1))
    );

    // A rising y requires no input to be 1.
    check_y_rise_requires_no_high: assert property (
        @(posedge CLK) disable iff (1'b0)
        $rose(y) |-> ((p1 !== 1'b1) && (p2 !== 1'b1) && (p3 !== 1'b1) && (p4 !== 1'b1) && (p5 !== 1'b1))
    );

    // With all inputs known 0/1, y equals logical NOR of inputs.
    check_boolean_equivalence_when_inputs_known: assert property (
        @(posedge CLK) disable iff (1'b0)
        ((p1 === 1'b0 || p1 === 1'b1) &&
         (p2 === 1'b0 || p2 === 1'b1) &&
         (p3 === 1'b0 || p3 === 1'b1) &&
         (p4 === 1'b0 || p4 === 1'b1) &&
         (p5 === 1'b0 || p5 === 1'b1)) |-> (y === !(p1 || p2 || p3 || p4 || p5))
    );
endmodule