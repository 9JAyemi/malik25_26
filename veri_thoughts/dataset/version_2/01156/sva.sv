module srlc32e_sva (
    input logic [31:0] D,
    input logic CLK,
    input logic CE,
    input logic A,
    input logic Q,
    // Internal signal from RTL
    input logic [31:0] Q_reg
);
    // Clock: CLK. No reset in RTL.

    // Q reflects Q_reg indexed by A at each clock.
    check_q_matches_qreg_select: assert property (
        @(posedge CLK) Q == Q_reg[A]
    );

    // When A==0, Q equals Q_reg[0].
    check_select_a0: assert property (
        @(posedge CLK) (A == 1'b0) |-> (Q == Q_reg[0])
    );

    // When A==1, Q equals Q_reg[1].
    check_select_a1: assert property (
        @(posedge CLK) (A == 1'b1) |-> (Q == Q_reg[1])
    );

    // With CE high, Q_reg loads D on the next cycle.
    check_qreg_updates_on_ce: assert property (
        @(posedge CLK) CE |=> (Q_reg == $past(D))
    );

    // With CE low, Q_reg holds its previous value.
    check_qreg_holds_on_noce: assert property (
        @(posedge CLK) !CE |=> (Q_reg == $past(Q_reg))
    );

    // After a CE capture, Q equals previous D indexed by next A.
    check_q_next_after_ce: assert property (
        @(posedge CLK) CE |=> (Q == $past(D)[A])
    );

    // With CE low, next Q equals previous Q_reg indexed by next A.
    check_q_next_after_noce: assert property (
        @(posedge CLK) !CE |=> (Q == $past(Q_reg)[A])
    );

    // If Q changes, either A or Q_reg must have changed.
    check_q_change_caused_by_a_or_qreg: assert property (
        @(posedge CLK) $changed(Q) |-> ($changed(A) || $changed(Q_reg))
    );

    // If A and Q_reg are stable, Q must be stable.
    check_stable_inputs_imply_stable_q: assert property (
        @(posedge CLK) ($stable(A) && $stable(Q_reg)) |-> $stable(Q)
    );

    // Any change in Q_reg must be due to CE being high in the prior cycle.
    check_qreg_change_requires_prior_ce: assert property (
        @(posedge CLK) $changed(Q_reg) |-> $past(CE)
    );

endmodule