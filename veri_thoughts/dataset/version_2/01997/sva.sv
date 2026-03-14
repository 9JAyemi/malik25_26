module my_module_sva (
    input logic CLK,      // External clock for sampling assertions
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);
    // Y must equal B1 | (A1 & A2).
    check_y_equals_or_and: assert property (
        @(posedge CLK) Y == (B1 || (A1 && A2))
    );

    // B1 HIGH forces Y HIGH.
    check_b1_implies_y_high: assert property (
        @(posedge CLK) B1 |-> Y
    );

    // A1&A2 HIGH forces Y HIGH.
    check_a1a2_implies_y_high: assert property (
        @(posedge CLK) (A1 && A2) |-> Y
    );

    // If B1=0 and !(A1&A2), then Y must be 0.
    check_blocking_inputs_imply_y_low: assert property (
        @(posedge CLK) (!B1 && !(A1 && A2)) |-> (!Y)
    );

    // Y=0 implies B1=0 and !(A1&A2).
    check_y_low_implies_blocking_inputs: assert property (
        @(posedge CLK) (!Y) |-> (!B1 && !(A1 && A2))
    );

    // When A1&A2=0, Y equals B1.
    check_y_equals_b1_when_and_zero: assert property (
        @(posedge CLK) (!(A1 && A2)) |-> (Y == B1)
    );

    // When B1=0, Y equals A1&A2.
    check_y_equals_and_when_b1_zero: assert property (
        @(posedge CLK) (!B1) |-> (Y == (A1 && A2))
    );

    // With known inputs, Y is not X/Z.
    check_known_inputs_imply_known_y: assert property (
        @(posedge CLK) (!$isunknown({A1, A2, B1})) |-> (!$isunknown(Y))
    );

    // All inputs LOW => Y LOW.
    check_all_zero_inputs_imply_y_low: assert property (
        @(posedge CLK) (!B1 && !A1 && !A2) |-> (!Y)
    );

    // Y=1 implies B1=1 or A1&A2=1.
    check_y_high_implies_source: assert property (
        @(posedge CLK) (Y) |-> (B1 || (A1 && A2))
    );
endmodule