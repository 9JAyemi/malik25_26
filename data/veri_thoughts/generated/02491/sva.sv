module four_to_one_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);
    // No clock/reset in RTL; pure combinational X = A1 | A2 | B1 | B2.
    // Sample on any input/output edge.

    // X must equal the OR of inputs on any change.
    check_or_equation: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            (X === (A1 | A2 | B1 | B2))
    );

    // If X is HIGH, at least one input is HIGH.
    check_x_high_implies_some_input_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            (X === 1'b1) |-> ##0 ((A1 === 1'b1) || (A2 === 1'b1) || (B1 === 1'b1) || (B2 === 1'b1))
    );

    // If X is LOW, all inputs are LOW.
    check_x_low_implies_all_inputs_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            (X === 1'b0) |-> ##0 ((A1 === 1'b0) && (A2 === 1'b0) && (B1 === 1'b0) && (B2 === 1'b0))
    );

    // A1 HIGH implies X HIGH.
    check_a1_high_implies_x_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            (A1 === 1'b1) |-> ##0 (X === 1'b1)
    );

    // A2 HIGH implies X HIGH.
    check_a2_high_implies_x_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            (A2 === 1'b1) |-> ##0 (X === 1'b1)
    );

    // B1 HIGH implies X HIGH.
    check_b1_high_implies_x_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            (B1 === 1'b1) |-> ##0 (X === 1'b1)
    );

    // B2 HIGH implies X HIGH.
    check_b2_high_implies_x_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            (B2 === 1'b1) |-> ##0 (X === 1'b1)
    );

    // A1 controls X when other inputs are LOW: X equals A1.
    check_a1_controls_when_others_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            ((A2 === 1'b0) && (B1 === 1'b0) && (B2 === 1'b0)) |-> ##0 (X === A1)
    );

    // A2 controls X when other inputs are LOW: X equals A2.
    check_a2_controls_when_others_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            ((A1 === 1'b0) && (B1 === 1'b0) && (B2 === 1'b0)) |-> ##0 (X === A2)
    );

    // B1 controls X when other inputs are LOW: X equals B1.
    check_b1_controls_when_others_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            ((A1 === 1'b0) && (A2 === 1'b0) && (B2 === 1'b0)) |-> ##0 (X === B1)
    );

    // B2 controls X when other inputs are LOW: X equals B2.
    check_b2_controls_when_others_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            ((A1 === 1'b0) && (A2 === 1'b0) && (B1 === 1'b0)) |-> ##0 (X === B2)
    );

    // A rising edge on X implies at least one input is now HIGH.
    check_x_rise_requires_input_high: assert property (
        @(posedge X) ##0 ((A1 === 1'b1) || (A2 === 1'b1) || (B1 === 1'b1) || (B2 === 1'b1))
    );

    // A falling edge on X implies all inputs are now LOW.
    check_x_fall_requires_all_inputs_low: assert property (
        @(negedge X) ##0 ((A1 === 1'b0) && (A2 === 1'b0) && (B1 === 1'b0) && (B2 === 1'b0))
    );

endmodule