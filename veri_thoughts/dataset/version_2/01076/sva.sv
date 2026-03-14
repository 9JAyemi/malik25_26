module flip_flop_sva (
    input logic Q,
    input logic Q_N,
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic CLK_N,
    input logic SET_B,
    input logic RESET_B
);

    // SCD=1 at a negedge forces next Q=0 and Q_N=1 (highest priority).
    check_scd_forces_q0: assert property (
        @(negedge CLK_N) (SCD == 1'b1) |=> (Q == 1'b0) && (Q_N == 1'b1)
    );

    // With SCD=0 and SCE=1 at a negedge, next Q=1 and Q_N=0.
    check_sce_forces_q1: assert property (
        @(negedge CLK_N) (SCD == 1'b0) && (SCE == 1'b1) |=> (Q == 1'b1) && (Q_N == 1'b0)
    );

    // With SCD=0, SCE=0, and SET_B=0 at a negedge, next Q=1 and Q_N=0.
    check_setb_low_forces_q1: assert property (
        @(negedge CLK_N) (SCD == 1'b0) && (SCE == 1'b0) && (SET_B == 1'b0) |=> (Q == 1'b1) && (Q_N == 1'b0)
    );

    // With SCD=0, SCE=0, SET_B=1, and RESET_B=0 at a negedge, next Q=0 and Q_N=1.
    check_resetb_low_forces_q0: assert property (
        @(negedge CLK_N) (SCD == 1'b0) && (SCE == 1'b0) && (SET_B == 1'b1) && (RESET_B == 1'b0) |=> (Q == 1'b0) && (Q_N == 1'b1)
    );

    // With no control active at a negedge, next Q follows prior D and Q_N is its inverse.
    check_default_loads_d: assert property (
        @(negedge CLK_N) (SCD == 1'b0) && (SCE == 1'b0) && (SET_B == 1'b1) && (RESET_B == 1'b1) |=> (Q == $past(D)) && (Q_N == ~$past(D))
    );

    // After any negedge update, Q_N is the bitwise complement of Q.
    check_outputs_complement_each_cycle: assert property (
        @(negedge CLK_N) 1'b1 |=> (Q_N == ~Q)
    );

    // If the default path occurs in back-to-back cycles and D is unchanged, Q and Q_N remain unchanged.
    check_hold_when_default_and_D_stable: assert property (
        @(negedge CLK_N)
            $past((SCD == 1'b0) && (SCE == 1'b0) && (SET_B == 1'b1) && (RESET_B == 1'b1)) &&
            (SCD == 1'b0) && (SCE == 1'b0) && (SET_B == 1'b1) && (RESET_B == 1'b1) &&
            (D == $past(D))
        |-> (Q == $past(Q)) && (Q_N == $past(Q_N))
    );

endmodule