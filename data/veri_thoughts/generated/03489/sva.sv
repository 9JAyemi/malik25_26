module RS232TX_sva (
    input logic clk,
    input logic Tx_start,
    input logic [23:0] dbuffer,
    input logic Tx,
    input logic Tx_busy,
    input logic bittick,
    input logic [3:0] Tx_state,
    input logic [7:0] Tx_shift
);

    // Tx_busy is high whenever the transmitter is not idle.
    check_busy_decode: assert property (
        @(posedge clk)
        Tx_busy == (Tx_state != 4'b0000)
    );

    // Tx follows the RTL decode from state and shift register.
    check_tx_decode: assert property (
        @(posedge clk)
        Tx == ((Tx_state < 4'b0100) | (Tx_state[3] & Tx_shift[0]))
    );

    // A start request in idle loads the low byte of dbuffer.
    check_start_load_shift: assert property (
        @(posedge clk)
        (Tx_state == 4'b0000 && Tx_start) |=> (Tx_shift == $past(dbuffer[7:0]))
    );

    // A start request in idle moves the FSM into the start-bit state.
    check_start_moves_to_start_state: assert property (
        @(posedge clk)
        (Tx_state == 4'b0000 && Tx_start) |=> (Tx_state == 4'b0100)
    );

    // Idle state holds when no start request is present.
    check_idle_holds_without_start: assert property (
        @(posedge clk)
        (Tx_state == 4'b0000 && !Tx_start) |=> (Tx_state == 4'b0000)
    );

    // The start-bit state advances to the first data-bit state on a tick.
    check_start_state_to_data0: assert property (
        @(posedge clk)
        (Tx_state == 4'b0100 && bittick) |=> (Tx_state == 4'b1000)
    );

    // Any non-idle state holds when there is no baud tick.
    check_active_holds_without_bittick: assert property (
        @(posedge clk)
        (Tx_state != 4'b0000 && !bittick) |=> (Tx_state == $past(Tx_state))
    );

    // Data-bit states 8 through 14 increment by one on each tick.
    check_data_states_increment_on_tick: assert property (
        @(posedge clk)
        (Tx_state[3] && (Tx_state != 4'b1111) && bittick) |=> (Tx_state == ($past(Tx_state) + 4'b0001))
    );

    // The last data-bit state advances to the first stop-bit state on a tick.
    check_last_data_to_stop1: assert property (
        @(posedge clk)
        (Tx_state == 4'b1111 && bittick) |=> (Tx_state == 4'b0010)
    );

    // The first stop-bit state advances to the second stop-bit state on a tick.
    check_stop1_to_stop2: assert property (
        @(posedge clk)
        (Tx_state == 4'b0010 && bittick) |=> (Tx_state == 4'b0011)
    );

    // The second stop-bit state returns to idle on a tick.
    check_stop2_to_idle: assert property (
        @(posedge clk)
        (Tx_state == 4'b0011 && bittick) |=> (Tx_state == 4'b0000)
    );

    // During data transmission, each tick shifts the transmit register right.
    check_shift_right_on_data_tick: assert property (
        @(posedge clk)
        (Tx_state[3] && bittick) |=> (Tx_shift == ($past(Tx_shift) >> 1))
    );

    // The shift register stays unchanged when neither load nor shift is enabled.
    check_shift_stable_without_load_or_shift: assert property (
        @(posedge clk)
        (!(Tx_state == 4'b0000 && Tx_start) && !(Tx_state[3] && bittick)) |=> $stable(Tx_shift)
    );

    // Illegal default-case states recover to idle on a tick.
    check_default_state_recovers_on_tick: assert property (
        @(posedge clk)
        (((Tx_state == 4'b0001) || (Tx_state == 4'b0101) || (Tx_state == 4'b0110) || (Tx_state == 4'b0111)) && bittick)
        |=> (Tx_state == 4'b0000)
    );

endmodule