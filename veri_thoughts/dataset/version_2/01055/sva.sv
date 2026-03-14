module my_full_adder_sva (
    input logic CLK,      // External clock for SVA sampling (DUT has no clock/reset)
    input logic A,
    input logic B,
    input logic CI,
    input logic SUM,
    input logic COUT
);
    ///// Functional correctness /////
    // SUM equals XOR of inputs.
    check_sum_matches_xor: assert property (
        @(posedge CLK) SUM == (A ^ B ^ CI)
    );
    // COUT equals majority-of-three of inputs.
    check_cout_majority: assert property (
        @(posedge CLK) COUT == ((A & B) | (A & CI) | (B & CI))
    );
    // 2-bit result {COUT,SUM} equals arithmetic sum of inputs.
    check_addition_consistency: assert property (
        @(posedge CLK) {COUT, SUM} == ({1'b0, A} + {1'b0, B} + {1'b0, CI})
    );

    ///// Parity toggle behavior /////
    // If only A changes and B,CI are stable, SUM must change.
    check_sum_toggles_on_A: assert property (
        @(posedge CLK) ($changed(A) && $stable(B) && $stable(CI)) |-> $changed(SUM)
    );
    // If only B changes and A,CI are stable, SUM must change.
    check_sum_toggles_on_B: assert property (
        @(posedge CLK) ($changed(B) && $stable(A) && $stable(CI)) |-> $changed(SUM)
    );
    // If only CI changes and A,B are stable, SUM must change.
    check_sum_toggles_on_CI: assert property (
        @(posedge CLK) ($changed(CI) && $stable(A) && $stable(B)) |-> $changed(SUM)
    );

    ///// Simplified cases derived from the equations /////
    // When B equals CI, SUM equals A.
    check_sum_equals_A_when_BeqCI: assert property (
        @(posedge CLK) (B == CI) |-> (SUM == A)
    );
    // When A equals B, SUM equals CI.
    check_sum_equals_CI_when_AeqB: assert property (
        @(posedge CLK) (A == B) |-> (SUM == CI)
    );
    // For inputs 000, outputs must be 00.
    check_truth_000: assert property (
        @(posedge CLK) (!A && !B && !CI) |-> (SUM == 1'b0 && COUT == 1'b0)
    );
    // For inputs 111, outputs must be 11.
    check_truth_111: assert property (
        @(posedge CLK) (A && B && CI) |-> (SUM == 1'b1 && COUT == 1'b1)
    );
endmodule