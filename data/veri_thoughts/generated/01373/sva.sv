module five_input_one_output_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic Y
);
    // Y matches the exact RTL expression
    check_function_equivalence_original: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge D1 or negedge D1)
            Y == ( ((A1 & A2) | (B1 & C1)) ? 1'b1 : (D1 ? 1'b0 : 1'b1) )
    );

    // Y equals simplified form: ~D1 | (A1&A2) | (B1&C1)
    check_function_equivalence_simplified: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge D1 or negedge D1)
            Y == ((~D1) | (A1 & A2) | (B1 & C1))
    );

    // If D1 is LOW, Y must be HIGH
    check_y_high_when_D1_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge D1 or negedge D1)
            (!D1) |-> (Y == 1'b1)
    );

    // If A1&A2 are both HIGH, Y must be HIGH
    check_y_high_when_A1_and_A2: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge D1 or negedge D1)
            ((A1 & A2) == 1'b1) |-> (Y == 1'b1)
    );

    // If B1&C1 are both HIGH, Y must be HIGH
    check_y_high_when_B1_and_C1: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge D1 or negedge D1)
            ((B1 & C1) == 1'b1) |-> (Y == 1'b1)
    );

    // If D1 is HIGH and neither pair is HIGH, Y must be LOW
    check_y_low_when_D1_high_and_no_pairs: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge D1 or negedge D1)
            (D1 & ~((A1 & A2) | (B1 & C1))) |-> (Y == 1'b0)
    );

    // If Y is LOW, D1 must be HIGH and no pair must be HIGH
    check_y_low_only_when_D1_high_and_no_pairs: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge D1 or negedge D1)
            (Y == 1'b0) |-> (D1 & ~((A1 & A2) | (B1 & C1)))
    );

    // If Y and D1 are HIGH, at least one pair (A1&A2 or B1&C1) must be HIGH
    check_y_high_with_D1_high_implies_pair: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge D1 or negedge D1)
            (Y & D1) |-> ((A1 & A2) | (B1 & C1))
    );

    // When no pairs are HIGH, Y equals ~D1
    check_y_equals_not_D1_when_no_pairs: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge D1 or negedge D1)
            (~((A1 & A2) | (B1 & C1))) |-> (Y == ~D1)
    );
endmodule