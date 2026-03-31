module mux_dff_sva (
    input logic CLK,
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic Q,
    input logic Q_N
);
    ///// Output relationship /////
    // Q_N is always the logical inverse of Q.
    check_qn_is_not_q: assert property (
        @(posedge CLK) Q_N == ~Q
    );

    ///// Sequential update behavior /////
    // Next-cycle Q equals: (SCD&~SCE)?D : (~SCD&SCE)?Q : 1'b0 (all signals from prior cycle).
    check_full_update_equation: assert property (
        @(posedge CLK)
            Q == ( ($past(SCD) && !$past(SCE)) ? $past(D)
                 : ((!$past(SCD) &&  $past(SCE)) ? $past(Q)
                 : 1'b0) )
    );

    // When SCD=1 and SCE=0, Q loads D on the next clock.
    check_load_d_when_scd1_sce0: assert property (
        @(posedge CLK) ($past(SCD) && !$past(SCE)) |=> (Q == $past(D))
    );

    // When SCD=0 and SCE=1, Q holds its previous value.
    check_hold_when_scd0_sce1: assert property (
        @(posedge CLK) (!$past(SCD) && $past(SCE)) |=> (Q == $past(Q))
    );

    // When SCD=0 and SCE=0, Q clears to 0.
    check_clear_when_00: assert property (
        @(posedge CLK) (!$past(SCD) && !$past(SCE)) |=> (Q == 1'b0)
    );

    // When SCD=1 and SCE=1, Q clears to 0.
    check_clear_when_11: assert property (
        @(posedge CLK) ($past(SCD) && $past(SCE)) |=> (Q == 1'b0)
    );

    ///// Transition causes (derived from update function) /////
    // A rising edge on Q must be caused by prior (SCD=1,SCE=0,D=1).
    check_q_rise_cause: assert property (
        @(posedge CLK) $rose(Q) |-> ($past(SCD) && !$past(SCE) && $past(D))
    );

    // A falling edge on Q must be caused by prior clear or loading D=0.
    check_q_fall_cause: assert property (
        @(posedge CLK) $fell(Q) |-> ( ($past(SCD) == $past(SCE)) || ($past(SCD) && !$past(SCE) && !$past(D)) )
    );
endmodule