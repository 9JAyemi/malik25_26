module d_flipflop_with_setreset_sva (
    input logic D,
    input logic SET_B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic CLK,
    input logic Q,
    input logic Q_N
);
    // Recreate internal set/reset signals from RTL
    logic S;
    logic R;
    assign S = (~SET_B) & VPB & VNB;
    assign R = ( SET_B) & VPB & VNB;

    // Q_N is always the complement of Q.
    check_qn_is_complement: assert property (
        @(posedge CLK) (Q_N == ~Q)
    );

    // S and R are never both asserted.
    check_sr_mutex: assert property (
        @(posedge CLK) !(S && R)
    );

    // Exactly one of S or R asserted iff VPB & VNB is HIGH.
    check_sr_xor_matches_power: assert property (
        @(posedge CLK) ((S ^ R) == (VPB & VNB))
    );

    // If S was asserted last cycle, Q is 1 this cycle.
    check_q_set_on_prev_S: assert property (
        @(posedge CLK) $past(S) |-> (Q == 1'b1)
    );

    // If R was asserted last cycle, Q is 0 this cycle.
    check_q_reset_on_prev_R: assert property (
        @(posedge CLK) $past(R) |-> (Q == 1'b0)
    );

    // If neither S nor R was asserted last cycle, Q follows D from last cycle.
    check_q_follows_D_when_prev_no_SR: assert property (
        @(posedge CLK) $past(!S && !R) |-> (Q == $past(D))
    );

    // Full next-state equation: Q equals last-cycle resolve of S/R/D.
    check_combined_update_rule: assert property (
        @(posedge CLK) Q == $past( S ? 1'b1 : (R ? 1'b0 : D) )
    );

    // With VPB & VNB HIGH last cycle, Q equals complement of last SET_B.
    check_q_function_when_power_good: assert property (
        @(posedge CLK) $past(VPB & VNB) |-> (Q == $past(~SET_B))
    );

    // With VPB & VNB HIGH last cycle, Q_N equals last SET_B.
    check_qn_function_when_power_good: assert property (
        @(posedge CLK) $past(VPB & VNB) |-> (Q_N == $past(SET_B))
    );

    // If neither S nor R was asserted last cycle, Q_N follows ~D from last cycle.
    check_qn_follows_nD_when_prev_no_SR: assert property (
        @(posedge CLK) $past(!S && !R) |-> (Q_N == $past(~D))
    );
endmodule