module my_and3_module_sva (
    input logic CLK,
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);
    ///// AND gate functional checks /////
    // Y must equal A & B & C.
    check_y_equals_and: assert property (
        @(posedge CLK) (Y == (A & B & C))
    );

    // If Y is HIGH, all inputs must be HIGH.
    check_y_high_requires_all_high: assert property (
        @(posedge CLK) Y |-> (A && B && C)
    );

    // If all inputs are HIGH, Y must be HIGH.
    check_all_high_implies_y_high: assert property (
        @(posedge CLK) (A && B && C) |-> Y
    );

    // If any input is LOW, Y must be LOW.
    check_any_low_implies_y_low: assert property (
        @(posedge CLK) ((!A) || (!B) || (!C)) |-> (!Y)
    );

    // Y can only rise when all inputs are HIGH.
    check_y_rise_requires_all_high: assert property (
        @(posedge CLK) $rose(Y) |-> (A && B && C)
    );

    // Y can only fall when any input is LOW.
    check_y_fall_requires_any_low: assert property (
        @(posedge CLK) $fell(Y) |-> ((!A) || (!B) || (!C))
    );
endmodule