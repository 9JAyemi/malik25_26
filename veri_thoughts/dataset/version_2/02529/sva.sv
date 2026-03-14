module add_sub_carry_out_sva (
    input logic CLK,
    input logic [3:0] S,
    input logic [30:0] Q_reg,
    input logic [6:0] Q,
    input logic FSM_exp_operation_A_S,
    input logic [1:0] FSM_selector_B,
    input logic DI
);

    // S equals low 4 bits of ({1'b0,Q_reg} + {1'b0,Q}) when add is selected.
    add_low_nibble_matches_full_add: assert property (
        @(posedge CLK) FSM_exp_operation_A_S |-> ( S == ( ({1'b0, Q_reg} + {1'b0, Q})[3:0] ) )
    );

    // S equals low 4 bits of ({1'b0,Q_reg} - {1'b0,Q}) when subtract is selected.
    sub_low_nibble_matches_full_sub: assert property (
        @(posedge CLK) !FSM_exp_operation_A_S |-> ( S == ( ({1'b0, Q_reg} - {1'b0, Q})[3:0] ) )
    );

    // DI has no effect on S when other relevant inputs are stable.
    s_independent_of_DI_changes: assert property (
        @(posedge CLK) ($stable(Q) && $stable(Q_reg) && $stable(FSM_exp_operation_A_S) && !$stable(DI)) |-> $stable(S)
    );

    // FSM_selector_B has no effect on S when other relevant inputs are stable.
    s_independent_of_selectorB_changes: assert property (
        @(posedge CLK) ($stable(Q) && $stable(Q_reg) && $stable(FSM_exp_operation_A_S) && !$stable(FSM_selector_B)) |-> $stable(S)
    );

    // Changes to Q[6:4] do not affect S when other relevant inputs are stable.
    s_independent_of_Q_upper_bits: assert property (
        @(posedge CLK) ($stable(Q_reg) && $stable(FSM_exp_operation_A_S) && $stable(Q[3:0]) && !$stable(Q[6:4])) |-> $stable(S)
    );

    // Changes to Q_reg[30:4] do not affect S when other relevant inputs are stable.
    s_independent_of_Qreg_upper_bits: assert property (
        @(posedge CLK) ($stable(Q) && $stable(FSM_exp_operation_A_S) && $stable(Q_reg[3:0]) && !$stable(Q_reg[30:4])) |-> $stable(S)
    );

    // When Q is zero, S equals Q_reg[3:0] for both add and subtract.
    s_passthrough_when_Q_zero: assert property (
        @(posedge CLK) (Q == 7'h00) |-> (S == Q_reg[3:0])
    );

    // When low nibbles of Q_reg and Q are zero, S is zero for both operations.
    s_zero_when_both_low_nibbles_zero: assert property (
        @(posedge CLK) (Q_reg[3:0] == 4'h0 && Q[3:0] == 4'h0) |-> (S == 4'h0)
    );

    // For add: S equals (Q_reg[3:0] + Q[3:0]) modulo 16.
    add_low_nibble_depends_only_on_low_nibbles: assert property (
        @(posedge CLK) FSM_exp_operation_A_S |-> ( S == ((Q_reg[3:0] + Q[3:0]) & 4'hF) )
    );

    // For subtract: S equals (Q_reg[3:0] - Q[3:0]) modulo 16.
    sub_low_nibble_depends_only_on_low_nibbles: assert property (
        @(posedge CLK) !FSM_exp_operation_A_S |-> ( S == ((Q_reg[3:0] - Q[3:0]) & 4'hF) )
    );

endmodule