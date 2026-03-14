module UART_Receiver_sva (
    input logic       Clk,
    input logic       Reset,     // active-high synchronous reset in RTL (applied via tReset)
    input logic [7:0] Data,
    input logic       Ready,
    input logic       Ack,
    input logic       Rx
);
    // After previous-cycle Reset, Ready and Data must be cleared.
    check_reset_flush_outputs: assert property (
        @(posedge Clk) disable iff (Reset) $past(Reset) |-> (Ready == 1'b0) && (Data == 8'h00)
    );

    // After previous-cycle Ack, Ready and Data must be cleared.
    check_ack_flush_outputs: assert property (
        @(posedge Clk) disable iff (Reset) $past(Ack) |-> (Ready == 1'b0) && (Data == 8'h00)
    );

    // Ready cannot be high if Reset or Ack was high in the previous cycle.
    check_ready_blocked_by_prev_flush: assert property (
        @(posedge Clk) disable iff (Reset) Ready |-> (!$past(Reset) && !$past(Ack))
    );

    // If Ready and Ack are both high now, next cycle Ready/Data must clear.
    check_ready_ack_clears_next: assert property (
        @(posedge Clk) disable iff (Reset) (Ready && Ack) |=> (Ready == 1'b0) && (Data == 8'h00)
    );

    // A falling edge on Ready must be caused by previous-cycle Ack or Reset.
    check_ready_fall_requires_prev_flush: assert property (
        @(posedge Clk) disable iff (Reset) $fell(Ready) |-> ($past(Ack) || $past(Reset))
    );

    // Data may change only when Ready is asserted or when previous-cycle Ack/Reset flushed it.
    check_data_change_conditions: assert property (
        @(posedge Clk) disable iff (Reset) (Data != $past(Data)) |-> (Ready || $past(Ack) || $past(Reset))
    );

    // Once Ready is high, it stays high until a previous-cycle Ack/Reset occurs.
    check_ready_sticky_without_prev_flush: assert property (
        @(posedge Clk) disable iff (Reset) ($past(Ready) && !$past(Ack) && !$past(Reset)) |-> Ready
    );

    // While Ready remains high (and no previous-cycle Ack/Reset), Data must remain stable.
    check_data_stable_while_ready: assert property (
        @(posedge Clk) disable iff (Reset) ($past(Ready) && !$past(Ack) && !$past(Reset)) |-> (Data == $past(Data))
    );

    // Ready must not rise in the cycle after Ack was high.
    check_no_ready_rise_after_prev_ack: assert property (
        @(posedge Clk) disable iff (Reset) $past(Ack) |-> !$rose(Ready)
    );

    // Ready must not rise in the cycle after Reset was high.
    check_no_ready_rise_after_prev_reset: assert property (
        @(posedge Clk) disable iff (Reset) $past(Reset) |-> !$rose(Ready)
    );
endmodule