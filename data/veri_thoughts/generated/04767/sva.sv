module sky130_fd_sc_hs__sedfxbp_sva (
    input logic D,
    input logic DE,
    input logic SCD,
    input logic SCE,
    input logic VPWR,
    input logic VGND,
    input logic Q,
    input logic Q_N,
    input logic CLK
);

    // Q captures D on the enabled data-load condition.
    check_q_loads_d: assert property (
        @(posedge CLK)
        (SCD == 1'b0 && SCE == 1'b0 && DE == 1'b1 && VPWR == 1'b1 && VGND == 1'b0)
        |=> (Q == $past(D))
    );

    // Q_N captures the inverse of D on the enabled data-load condition.
    check_qn_loads_not_d: assert property (
        @(posedge CLK)
        (SCD == 1'b0 && SCE == 1'b0 && DE == 1'b1 && VPWR == 1'b1 && VGND == 1'b0)
        |=> (Q_N == ~$past(D))
    );

    // The alternate control pattern forces Q low.
    check_q_forced_low: assert property (
        @(posedge CLK)
        (SCD == 1'b1 && SCE == 1'b1 && DE == 1'b0 && VPWR == 1'b0 && VGND == 1'b1)
        |=> (Q == 1'b0)
    );

    // The alternate control pattern forces Q_N high.
    check_qn_forced_high: assert property (
        @(posedge CLK)
        (SCD == 1'b1 && SCE == 1'b1 && DE == 1'b0 && VPWR == 1'b0 && VGND == 1'b1)
        |=> (Q_N == 1'b1)
    );

    // Q holds its value when neither assignment branch is taken.
    check_q_holds_when_no_branch: assert property (
        @(posedge CLK)
        !((SCD == 1'b0 && SCE == 1'b0 && DE == 1'b1 && VPWR == 1'b1 && VGND == 1'b0) ||
          (SCD == 1'b1 && SCE == 1'b1 && DE == 1'b0 && VPWR == 1'b0 && VGND == 1'b1))
        |=> (Q == $past(Q))
    );

    // Q_N holds its value when neither assignment branch is taken.
    check_qn_holds_when_no_branch: assert property (
        @(posedge CLK)
        !((SCD == 1'b0 && SCE == 1'b0 && DE == 1'b1 && VPWR == 1'b1 && VGND == 1'b0) ||
          (SCD == 1'b1 && SCE == 1'b1 && DE == 1'b0 && VPWR == 1'b0 && VGND == 1'b1))
        |=> (Q_N == $past(Q_N))
    );

    // A data-load update produces complementary outputs.
    check_complement_after_data_load: assert property (
        @(posedge CLK)
        (SCD == 1'b0 && SCE == 1'b0 && DE == 1'b1 && VPWR == 1'b1 && VGND == 1'b0)
        |=> (Q_N == ~Q)
    );

    // The alternate control pattern also produces complementary outputs.
    check_complement_after_forced_state: assert property (
        @(posedge CLK)
        (SCD == 1'b1 && SCE == 1'b1 && DE == 1'b0 && VPWR == 1'b0 && VGND == 1'b1)
        |=> (Q_N == ~Q)
    );

endmodule