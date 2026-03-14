module updown_counter_sva (
    input logic clk,
    input logic U_D,
    input logic [3:0] Q,
    input logic [3:0] Q_reg1,
    input logic [3:0] Q_reg2
);
    // Q_reg1 captures Q each cycle.
    check_q_reg1_captures_q: assert property (
        @(posedge clk) Q_reg1 == $past(Q)
    );

    // Q_reg2 captures Q_reg1 each cycle.
    check_q_reg2_captures_q_reg1: assert property (
        @(posedge clk) Q_reg2 == $past(Q_reg1)
    );

    // Q_reg2 equals Q delayed by 2 cycles.
    check_q_reg2_two_cycle_delay_of_q: assert property (
        @(posedge clk) Q_reg2 == $past(Q, 2)
    );

    // When counting up, Q equals previous Q_reg2 + 1 (mod-16).
    check_q_update_from_q_reg2_up: assert property (
        @(posedge clk) U_D |-> (Q == ($past(Q_reg2) + 4'd1))
    );

    // When counting down, Q equals previous Q_reg2 - 1 (mod-16).
    check_q_update_from_q_reg2_down: assert property (
        @(posedge clk) (!U_D) |-> (Q == ($past(Q_reg2) - 4'd1))
    );

    // End-to-end: when counting up, Q equals Q from 3 cycles ago + 1.
    check_e2e_up_from_q_delay3: assert property (
        @(posedge clk) U_D |-> (Q == ($past(Q, 3) + 4'd1))
    );

    // End-to-end: when counting down, Q equals Q from 3 cycles ago - 1.
    check_e2e_down_from_q_delay3: assert property (
        @(posedge clk) (!U_D) |-> (Q == ($past(Q, 3) - 4'd1))
    );

    // Wrap on increment: F + 1 -> 0.
    check_wrap_up: assert property (
        @(posedge clk) (U_D && ($past(Q_reg2) == 4'hF)) |-> (Q == 4'h0)
    );

    // Wrap on decrement: 0 - 1 -> F.
    check_wrap_down: assert property (
        @(posedge clk) (!U_D && ($past(Q_reg2) == 4'h0)) |-> (Q == 4'hF)
    );

    // LSB always toggles relative to previous Q_reg2 for +/-1.
    check_lsb_toggle_vs_qreg2: assert property (
        @(posedge clk) Q[0] == ~($past(Q_reg2[0]))
    );
endmodule