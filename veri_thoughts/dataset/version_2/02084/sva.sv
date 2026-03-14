module d_latch_sva (
    input logic D,
    input logic NOTIFIER,
    input logic VPWR,
    input logic VGND,
    input logic GATE,
    input logic Q
);

    // Q next-state function on each posedge GATE matches RTL priority
    check_next_state_function: assert property (
        @(posedge GATE)
            1'b1 |=> (Q == (VPWR ? 1'b1 :
                       (VGND ? 1'b0 :
                       (NOTIFIER ? $past(D) : $past(Q)))))
    );

    // When VPWR is HIGH at posedge GATE, Q becomes 1 on the next cycle
    update_q_to_one_when_vpwr_high: assert property (
        @(posedge GATE) VPWR |=> (Q == 1'b1)
    );

    // When VPWR is LOW and VGND is HIGH at posedge GATE, Q becomes 0 on the next cycle
    update_q_to_zero_when_vgnd_high_and_vpwr_low: assert property (
        @(posedge GATE) (!VPWR && VGND) |=> (Q == 1'b0)
    );

    // When both rails are LOW and NOTIFIER is HIGH at posedge GATE, Q captures D on next cycle
    latch_d_when_rails_low_and_notifier_high: assert property (
        @(posedge GATE) (!VPWR && !VGND && NOTIFIER) |=> (Q == $past(D))
    );

    // When both rails are LOW and NOTIFIER is LOW at posedge GATE, Q holds its previous value
    hold_q_when_no_controls_active: assert property (
        @(posedge GATE) (!VPWR && !VGND && !NOTIFIER) |=> (Q == $past(Q))
    );

endmodule