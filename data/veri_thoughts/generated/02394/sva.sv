module sky130_fd_sc_hs__fa_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic CIN,
    input logic VPWR,
    input logic VGND,
    input logic COUT,
    input logic SUM
);
    ///// Functional correctness for known inputs /////
    // With known inputs, SUM equals A ^ B ^ CIN.
    check_sum_matches_xor_when_known: assert property (
        @(posedge CLK) (!$isunknown({A,B,CIN})) |-> (SUM == (A ^ B ^ CIN))
    );
    // With known inputs, COUT equals (A&B) | (B&CIN) | (CIN&A).
    check_cout_matches_majority_when_known: assert property (
        @(posedge CLK) (!$isunknown({A,B,CIN})) |-> (COUT == ((A & B) | (B & CIN) | (CIN & A)))
    );

    ///// X-propagation /////
    // Any unknown on A/B/CIN drives SUM and COUT unknown.
    check_unknown_input_forces_unknown_outputs: assert property (
        @(posedge CLK) ($isunknown(A) || $isunknown(B) || $isunknown(CIN)) |-> ($isunknown(SUM) && $isunknown(COUT))
    );
    // Known A/B/CIN imply SUM and COUT are not unknown.
    check_outputs_known_if_inputs_known: assert property (
        @(posedge CLK) (!$isunknown({A,B,CIN})) |-> (!$isunknown({SUM,COUT}))
    );

    ///// Combinational stability /////
    // If A/B/CIN are stable, SUM/COUT remain stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({A,B,CIN}) |-> $stable({SUM,COUT})
    );
    // Any change on SUM/COUT must be due to a change on A/B/CIN.
    check_output_change_requires_input_change: assert property (
        @(posedge CLK) $changed({SUM,COUT}) |-> !$stable({A,B,CIN})
    );

    ///// Truth table spots (for known inputs) /////
    // 000 -> SUM=0, COUT=0.
    truth_all_zeros: assert property (
        @(posedge CLK) (A==1'b0 && B==1'b0 && CIN==1'b0) |-> (SUM==1'b0 && COUT==1'b0)
    );
    // Exactly one high -> SUM=1, COUT=0.
    truth_exactly_one_high: assert property (
        @(posedge CLK)
        (
            (A==1'b1 && B==1'b0 && CIN==1'b0) ||
            (A==1'b0 && B==1'b1 && CIN==1'b0) ||
            (A==1'b0 && B==1'b0 && CIN==1'b1)
        ) |-> (SUM==1'b1 && COUT==1'b0)
    );
    // Exactly two high -> SUM=0, COUT=1.
    truth_exactly_two_high: assert property (
        @(posedge CLK)
        (
            (A==1'b1 && B==1'b1 && CIN==1'b0) ||
            (A==1'b1 && B==1'b0 && CIN==1'b1) ||
            (A==1'b0 && B==1'b1 && CIN==1'b1)
        ) |-> (SUM==1'b0 && COUT==1'b1)
    );
    // 111 -> SUM=1, COUT=1.
    truth_all_ones: assert property (
        @(posedge CLK) (A==1'b1 && B==1'b1 && CIN==1'b1) |-> (SUM==1'b1 && COUT==1'b1)
    );
endmodule