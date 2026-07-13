module sky130_fd_sc_ls__o211ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    // Y implements ~(C1 & (A1 | A2) & B1).
    check_function_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge Y or negedge Y)
            Y == ~(C1 & (A1 | A2) & B1)
    );

    // Y is LOW only when C1, B1, and (A1|A2) are HIGH.
    check_low_output_condition: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge Y or negedge Y)
            (C1 & B1 & (A1 | A2)) |-> (Y == 1'b0)
    );

    // C1 LOW forces Y HIGH.
    check_high_when_C1_low: assert property (
        @(posedge C1 or negedge C1 or posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge Y or negedge Y)
            (C1 == 1'b0) |-> (Y == 1'b1)
    );

    // B1 LOW forces Y HIGH.
    check_high_when_B1_low: assert property (
        @(posedge B1 or negedge B1 or posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge C1 or negedge C1 or posedge Y or negedge Y)
            (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // A1 and A2 both LOW force Y HIGH.
    check_high_when_A1A2_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge Y or negedge Y)
            ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // Y LOW implies C1 and B1 HIGH and (A1|A2) HIGH.
    check_low_implies_inputs_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge Y or negedge Y)
            (Y == 1'b0) |-> (C1 == 1'b1) && (B1 == 1'b1) && ((A1 | A2) == 1'b1)
    );

    // DeMorgan form: Y == (~C1) | (~B1) | ((~A1) & (~A2)).
    check_demorgan_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge Y or negedge Y)
            Y == ((~C1) | (~B1) | ((~A1) & (~A2)))
    );

    // With C1 and B1 HIGH and A2 LOW, Y equals ~A1.
    check_reduction_when_A2_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge Y or negedge Y)
            (C1 && B1 && (A2 == 1'b0)) |-> (Y == ~A1)
    );

    // With C1 and B1 HIGH and A1 LOW, Y equals ~A2.
    check_reduction_when_A1_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge Y or negedge Y)
            (C1 && B1 && (A1 == 1'b0)) |-> (Y == ~A2)
    );

    // When (A1|A2) and B1 are HIGH, Y equals ~C1.
    check_reduction_when_or_and_B1_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge Y or negedge Y)
            ((A1 | A2) && B1) |-> (Y == ~C1)
    );

    // When C1 and (A1|A2) are HIGH, Y equals ~B1.
    check_reduction_when_or_and_C1_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge Y or negedge Y)
            (C1 && (A1 | A2)) |-> (Y == ~B1)
    );

    // A1 HIGH with B1 and C1 HIGH forces Y LOW.
    check_A1_high_forces_low: assert property (
        @(posedge A1 or negedge A1 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge A2 or negedge A2 or posedge Y or negedge Y)
            (A1 && B1 && C1) |-> (Y == 1'b0)
    );

    // A2 HIGH with B1 and C1 HIGH forces Y LOW.
    check_A2_high_forces_low: assert property (
        @(posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge A1 or negedge A1 or posedge Y or negedge Y)
            (A2 && B1 && C1) |-> (Y == 1'b0)
    );

    // A falling edge on Y implies all NAND inputs are HIGH.
    check_y_fall_requires_all_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge Y or negedge Y)
            $fell(Y) |-> (C1 && B1 && (A1 | A2))
    );

    // A rising edge on Y implies at least one NAND input is LOW.
    check_y_rise_requires_any_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1 or posedge Y or negedge Y)
            $rose(Y) |-> ((!C1) || (!B1) || (!(A1 | A2)))
    );
endmodule