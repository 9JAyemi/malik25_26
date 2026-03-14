module flip_flop_sva (
    input logic CLK,
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic SET_B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Q,
    input logic Q_N
);

    ///// Output relationship /////
    // Q_N is always the logical inverse of Q.
    check_qn_is_inverse_of_q: assert property (
        @(posedge CLK) Q_N == ~Q
    );

    ///// Next-state behavior of Q /////
    // If Q=1 and SCE=0, Q stays 1 next cycle.
    check_hold_one_when_sce_low: assert property (
        @(posedge CLK) (Q && (SCE == 1'b0)) |=> (Q == 1'b1)
    );
    // If Q=1 and SCE=1, Q becomes 0 next cycle.
    check_clear_when_sce_high: assert property (
        @(posedge CLK) (Q && (SCE == 1'b1)) |=> (Q == 1'b0)
    );
    // If Q=0 and SCD=1, Q becomes 1 next cycle.
    check_set_when_scd_high: assert property (
        @(posedge CLK) ((!Q) && (SCD == 1'b1)) |=> (Q == 1'b1)
    );
    // If Q=0 and SCD=0, Q stays 0 next cycle.
    check_hold_zero_when_scd_low: assert property (
        @(posedge CLK) ((!Q) && (SCD == 1'b0)) |=> (Q == 1'b0)
    );

    ///// Edge-cause checks /////
    // A falling edge on Q requires SCE was 1 in the prior cycle.
    check_q_fall_requires_sce_high: assert property (
        @(posedge CLK) $fell(Q) |-> $past(SCE)
    );
    // A rising edge on Q requires SCD was 1 in the prior cycle.
    check_q_rise_requires_scd_high: assert property (
        @(posedge CLK) $rose(Q) |-> $past(SCD)
    );

    ///// Complement edge correlation /////
    // When Q rises, Q_N falls the same cycle.
    check_qn_falls_when_q_rises: assert property (
        @(posedge CLK) $rose(Q) |-> $fell(Q_N)
    );
    // When Q falls, Q_N rises the same cycle.
    check_qn_rises_when_q_falls: assert property (
        @(posedge CLK) $fell(Q) |-> $rose(Q_N)
    );

endmodule