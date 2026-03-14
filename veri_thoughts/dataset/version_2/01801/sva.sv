module flip_flop_sva (
    input logic Q,
    input logic Q_N,
    input logic CLK,
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    ///// Combinational relation /////
    // Q_N is always the bitwise complement of Q.
    check_qn_complement: assert property (
        @(posedge CLK) Q_N == ~Q
    );

    ///// Sequential update rules (sampled one cycle later using $past) /////
    // Full next-state function encoded from the RTL if/else chain.
    check_next_state_function: assert property (
        @(posedge CLK) Q == ($past(SCE) ? 1'b0 : ($past(SCD) ? 1'b1 : $past(D)))
    );

    // When SCE was HIGH, Q is forced LOW.
    check_clear_on_sce: assert property (
        @(posedge CLK) $past(SCE) |-> (Q == 1'b0)
    );

    // When SCE was LOW and SCD was HIGH, Q is set HIGH.
    check_set_on_scd_when_sce_low: assert property (
        @(posedge CLK) (!$past(SCE) && $past(SCD)) |-> (Q == 1'b1)
    );

    // When both SCE and SCD were LOW, Q loads D.
    check_load_d_when_both_low: assert property (
        @(posedge CLK) (!$past(SCE) && !$past(SCD)) |-> (Q == $past(D))
    );

    // When both SCE and SCD were HIGH, Q is forced LOW.
    check_clear_when_both_high: assert property (
        @(posedge CLK) ($past(SCE) && $past(SCD)) |-> (Q == 1'b0)
    );

    // Loading D causes Q to change if D differed from prior Q.
    check_load_d_changes_q: assert property (
        @(posedge CLK) (!$past(SCE) && !$past(SCD) && ($past(D) != $past(Q))) |-> (Q != $past(Q))
    );

    // Loading D holds Q if D equaled prior Q.
    check_load_d_holds_q: assert property (
        @(posedge CLK) (!$past(SCE) && !$past(SCD) && ($past(D) == $past(Q))) |-> (Q == $past(Q))
    );
endmodule