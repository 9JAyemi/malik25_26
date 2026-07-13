module ring_counter_sva (
    input logic clk,
    input logic enable,
    input logic reset,
    input logic [3:0] q,
    input logic [3:0] q_reg
);
    ///// Reset behavior /////
    // On reset, q_reg is cleared to 0000 on the next cycle.
    reset_clears_qreg_next: assert property (
        @(posedge clk) reset |-> ##1 (q_reg == 4'b0000)
    );
    // On reset, q holds its value into the next cycle (no assignment under reset).
    reset_holds_q_across_cycle: assert property (
        @(posedge clk) reset |-> ##1 (q == $past(q))
    );

    ///// Enable/rotate behavior for q_reg /////
    // When enabled, q_reg[0] takes previous q_reg[3] on the next cycle.
    rotate_qreg_bit0_on_enable: assert property (
        @(posedge clk) disable iff (reset) enable |-> ##1 (q_reg[0] == $past(q_reg[3]))
    );
    // When enabled, q_reg[1] takes previous q_reg[0] on the next cycle.
    rotate_qreg_bit1_on_enable: assert property (
        @(posedge clk) disable iff (reset) enable |-> ##1 (q_reg[1] == $past(q_reg[0]))
    );
    // When enabled, q_reg[2] takes previous q_reg[1] on the next cycle.
    rotate_qreg_bit2_on_enable: assert property (
        @(posedge clk) disable iff (reset) enable |-> ##1 (q_reg[2] == $past(q_reg[1]))
    );
    // When enabled, q_reg[3] takes previous q_reg[2] on the next cycle.
    rotate_qreg_bit3_on_enable: assert property (
        @(posedge clk) disable iff (reset) enable |-> ##1 (q_reg[3] == $past(q_reg[2]))
    );

    ///// Output update timing /////
    // When enabled, q captures the previous q_reg on the next cycle.
    q_updates_from_prev_qreg_on_enable: assert property (
        @(posedge clk) disable iff (reset) enable |-> ##1 (q == $past(q_reg))
    );

    ///// Hold behavior when disabled /////
    // When disabled, q_reg holds its value into the next cycle.
    qreg_stable_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |-> ##1 $stable(q_reg)
    );
    // When disabled, q holds its value into the next cycle.
    q_stable_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |-> ##1 $stable(q)
    );

    ///// Update causality /////
    // Any change on q must be caused by enable in the previous cycle.
    q_change_requires_prev_enable: assert property (
        @(posedge clk) disable iff (reset) $changed(q) |-> $past(enable)
    );
endmodule