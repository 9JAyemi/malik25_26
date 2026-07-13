module sky130_fd_sc_ms__sdfbbn_sva (
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic CLK,
    input logic SET_B,
    input logic RESET_B,
    input logic Q,
    input logic Q_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Clock: CLK. Resets: SET_B, RESET_B (active-low, synchronous).
    // Sequential FF with priority: SCD > SCE > !RESET_B > !SET_B. Q = ~Q_N.

    // Q is always inverse of Q_N.
    check_q_inverts_qn: assert property (
        @(posedge CLK) disable iff (!SET_B || !RESET_B) (Q == ~Q_N)
    );

    // SCD high forces Q_N to 0 on the next cycle.
    check_scd_forces_zero: assert property (
        @(posedge CLK) disable iff (!SET_B || !RESET_B) SCD |=> (Q_N == 1'b0)
    );

    // With SCE high and SCD low, Q_N loads D on the next cycle.
    check_sce_loads_d_no_scd: assert property (
        @(posedge CLK) disable iff (!SET_B || !RESET_B) (SCE && !SCD) |=> (Q_N == $past(D))
    );

    // With RESET_B low and no later overrides, Q_N goes to 0 on the next cycle.
    check_reset_forces_zero_when_unoverridden: assert property (
        @(posedge CLK) (RESET_B == 1'b0) && (SCE == 1'b0) && (SCD == 1'b0) |=> (Q_N == 1'b0)
    );

    // With SET_B low and no later overrides, Q_N goes to 1 on the next cycle.
    check_set_forces_one_when_unoverridden: assert property (
        @(posedge CLK) (SET_B == 1'b0) && (RESET_B == 1'b1) && (SCE == 1'b0) && (SCD == 1'b0) |=> (Q_N == 1'b1)
    );

    // If SET_B and RESET_B both low (no SCE/SCD), RESET_B wins driving 0.
    check_reset_overrides_set: assert property (
        @(posedge CLK) (SET_B == 1'b0) && (RESET_B == 1'b0) && (SCE == 1'b0) && (SCD == 1'b0) |=> (Q_N == 1'b0)
    );

    // If RESET_B low and SCE high (no SCD), SCE overrides and Q_N loads D.
    check_sce_overrides_reset: assert property (
        @(posedge CLK) (RESET_B == 1'b0) && (SCE == 1'b1) && (SCD == 1'b0) |=> (Q_N == $past(D))
    );

    // When SET_B, RESET_B deasserted and SCE/SCD low, Q_N holds its value.
    check_hold_when_no_ctrls: assert property (
        @(posedge CLK) disable iff (!SET_B || !RESET_B) (SET_B == 1'b1) && (RESET_B == 1'b1) && (SCE == 1'b0) && (SCD == 1'b0) |=> (Q_N == $past(Q_N))
    );

    // After SCE load (no SCD), Q reflects ~D on next cycle.
    check_q_updates_after_sce: assert property (
        @(posedge CLK) disable iff (!SET_B || !RESET_B) (SCE && !SCD) |=> (Q == ~$past(D))
    );

    // After SCD high, Q goes to 1 on the next cycle.
    check_q_one_after_scd: assert property (
        @(posedge CLK) disable iff (!SET_B || !RESET_B) SCD |=> (Q == 1'b1)
    );
endmodule