module avr109rx_sva #(
    parameter int CLK_FREQUENCY = 1000000,
    parameter int BAUD_RATE     = 19200,
    parameter int BAUDDIV       = (CLK_FREQUENCY / BAUD_RATE),
    parameter int LOG2_BAUDDIV  = (BAUDDIV <= 1) ? 1 : $clog2(BAUDDIV)
)(
    input  logic              rst,
    input  logic              clk,
    input  logic [7:0]        rx_data,
    input  logic              rx_avail,
    input  logic              rxd,
    input  logic              rx_enabled,
    // Internal state from DUT
    input  logic [7:0]        rxshift_q,
    input  logic              rx_active_q,
    input  logic              rx_done_q,
    input  logic [3:0]        rxcnt_q,
    input  logic [LOG2_BAUDDIV-1:0] rxbaud_q
);

    localparam int BAUDDIV_M1   = BAUDDIV - 1;
    localparam int BAUDDIV_HALF = BAUDDIV/2;

    ///// Reset/disable behavior /////
    // When rst asserted or rx_enabled deasserted, outputs are driven LOW/zero.
    reset_outputs_zero: assert property (
        @(posedge clk) (rst | ~rx_enabled) |-> (rx_data == 8'h00) && (rx_avail == 1'b0)
    );
    // When rst asserted or rx_enabled deasserted, internal state clears to zero.
    reset_regs_zero: assert property (
        @(posedge clk) (rst | ~rx_enabled) |-> (rxshift_q == 8'h00) && (rx_active_q == 1'b0) &&
                                           (rx_done_q == 1'b0) && (rxcnt_q == 4'd0) &&
                                           (rxbaud_q == '0)
    );

    ///// Output mapping to internal state /////
    // rx_data mirrors rxshift_q every cycle.
    map_rx_data_to_shift: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled) (rx_data == rxshift_q)
    );
    // rx_avail mirrors rx_done_q every cycle.
    map_rx_avail_to_done: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled) (rx_avail == rx_done_q)
    );

    ///// rx_avail pulse semantics /////
    // rx_avail is a single-cycle pulse.
    rx_avail_one_cycle_pulse: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled) $rose(rx_avail) |=> !rx_avail
    );
    // When rx_avail is high, the receiver is inactive that same cycle.
    rx_avail_implies_inactive: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled) rx_avail |-> !rx_active_q
    );
    // Rising rx_avail corresponds to a stop-bit sample in the previous cycle.
    rx_avail_prev_stop_condition: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled)
            $rose(rx_avail) |-> $past(rx_active_q && (rxbaud_q == BAUDDIV_M1) && (rxcnt_q == 4'd9) && rxd)
    );
    // When rx_avail is high, rxcnt_q is 9 (stop-bit sample just occurred).
    rx_avail_implies_rxcnt9: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled) rx_avail |-> (rxcnt_q == 4'd9)
    );

    ///// Activation/deactivation rules /////
    // rx_active deasserts only following a valid stop-bit sample.
    rx_active_fall_only_on_stop: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled)
            $fell(rx_active_q) |-> $past((rxbaud_q == BAUDDIV_M1) && (rxcnt_q == 4'd9) && rxd)
    );
    // A detected start (idle with rxd low) activates reception on the next cycle.
    idle_start_on_low_rxd: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled) (!rx_active_q && !rxd) |=> rx_active_q
    );
    // While idle and rxd high, stay idle on the next cycle.
    idle_hold_on_high_rxd: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled) (!rx_active_q && rxd) |=> !rx_active_q
    );

    ///// Idle defaults /////
    // While idle, next-state defaults: shift=0, cnt=0, baud=BAUDDIV/2.
    idle_defaults_on_next: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled)
            !rx_active_q |=> (rxshift_q == 8'h00) && (rxcnt_q == 4'd0) && (rxbaud_q == BAUDDIV_HALF)
    );

    ///// Timing and sampling behavior while active /////
    // Between samples, baud counter increments by 1; others hold; rx_done_q stays 0.
    active_between_samples_baud_increments: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled)
            (rx_active_q && (rxbaud_q != BAUDDIV_M1))
            |=> (rxbaud_q == $past(rxbaud_q) + 1) &&
                (rxcnt_q == $past(rxcnt_q)) &&
                (rxshift_q == $past(rxshift_q)) &&
                (rx_active_q == 1'b1) &&
                (rx_done_q == 1'b0)
    );
    // On any sample event, baud counter resets to 0 on the next cycle.
    sample_resets_baud: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled)
            (rx_active_q && (rxbaud_q == BAUDDIV_M1)) |=> (rxbaud_q == '0)
    );
    // Sample with rxcnt<9: shift in rxd at MSB, increment count, stay active, no done.
    active_sample_shift_and_count: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled)
            (rx_active_q && (rxbaud_q == BAUDDIV_M1) && (rxcnt_q < 4'd9))
            |=> (rx_active_q == 1'b1) &&
                (rxcnt_q == $past(rxcnt_q) + 1) &&
                (rxshift_q == { $past(rxd), $past(rxshift_q[7:1]) }) &&
                (rxbaud_q == '0) &&
                (rx_done_q == 1'b0)
    );
    // Sample stop bit (rxcnt==9) with rxd==1: deactivate and pulse done next cycle.
    active_stop_sample_done: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled)
            (rx_active_q && (rxbaud_q == BAUDDIV_M1) && (rxcnt_q == 4'd9) && rxd)
            |=> (!rx_active_q && rx_done_q && (rxbaud_q == '0))
    );
    // Sample stop bit (rxcnt==9) with rxd==0: remain active, hold count, no done, reset baud.
    active_stop_zero_waits: assert property (
        @(posedge clk) disable iff (rst | ~rx_enabled)
            (rx_active_q && (rxbaud_q == BAUDDIV_M1) && (rxcnt_q == 4'd9) && !rxd)
            |=> (rx_active_q && (rxcnt_q == 4'd9) && (rxbaud_q == '0) &&
                 (rxshift_q == $past(rxshift_q)) && (rx_done_q == 1'b0))
    );

endmodule