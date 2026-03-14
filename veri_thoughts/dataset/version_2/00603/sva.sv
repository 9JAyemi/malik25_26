module rc5_sva #(
    parameter csr_addr = 4'h0,
    parameter clk_freq = 100000000
) (
    input logic sys_clk,
    input logic sys_rst,

    input logic [13:0] csr_a,
    input logic csr_we,
    input logic [31:0] csr_di,
    input logic [31:0] csr_do,

    input logic rx_irq,
    input logic rx,

    // Internal DUT signals
    input logic [15:0] enable16_counter,
    input logic enable16,
    input logic rx1,
    input logic rx2,
    input logic rx_busy,
    input logic [3:0] rx_count16,
    input logic [3:0] rx_bitcount,
    input logic [12:0] rx_reg,
    input logic [12:0] rx_data,
    input logic csr_selected
);
    localparam int unsigned divisor = clk_freq/596/16;

    ///// Reset behavior /////
    // enable16_counter loads divisor-1 on reset.
    reset_enable16_counter: assert property (
        @(posedge sys_clk) sys_rst |-> (enable16_counter == (divisor - 1))
    );
    // RX control signals clear on reset.
    reset_rx_ctrl: assert property (
        @(posedge sys_clk) sys_rst |-> (rx_irq == 1'b0 && rx_busy == 1'b0 && rx_count16 == 4'd0 && rx_bitcount == 4'd0)
    );
    // csr_do clears on reset.
    reset_csr_do: assert property (
        @(posedge sys_clk) sys_rst |-> (csr_do == 32'd0)
    );

    ///// enable16 clock divider /////
    // enable16 is true iff counter is zero.
    check_enable16_definition: assert property (
        @(posedge sys_clk) disable iff (sys_rst) (enable16 == (enable16_counter == 16'd0))
    );
    // Counter reloads to divisor-1 when previous cycle had enable16 asserted.
    counter_reload_on_enable16: assert property (
        @(posedge sys_clk) disable iff (sys_rst) $past(!sys_rst) && $past(enable16) |-> (enable16_counter == (divisor - 1))
    );
    // Counter decrements by 1 otherwise.
    counter_decrement_otherwise: assert property (
        @(posedge sys_clk) disable iff (sys_rst) $past(!sys_rst) && !$past(enable16) |-> (enable16_counter == $past(enable16_counter) - 16'd1)
    );

    ///// RX input synchronizer /////
    // rx1 is rx delayed by one clock.
    rx1_pipeline: assert property (
        @(posedge sys_clk) disable iff (sys_rst) $past(!sys_rst) |-> (rx1 == $past(rx))
    );
    // rx2 is rx1 delayed by one clock.
    rx2_pipeline: assert property (
        @(posedge sys_clk) disable iff (sys_rst) $past(!sys_rst) |-> (rx2 == $past(rx1))
    );

    ///// RX state machine timing (gated by enable16) /////
    // rx_busy changes only on cycles where previous enable16 was high.
    rx_busy_changes_only_on_enable16: assert property (
        @(posedge sys_clk) disable iff (sys_rst) $past(!sys_rst) && (rx_busy != $past(rx_busy)) |-> $past(enable16)
    );
    // Rising rx_busy occurs only when previous cycle had enable16 and rx2 high (start bit detection).
    rx_busy_rise_on_startbit: assert property (
        @(posedge sys_clk) disable iff (sys_rst) (rx_busy && !$past(rx_busy)) |-> $past(enable16 && rx2)
    );
    // On rx_busy rise, counters initialize to 13 and 0 respectively.
    rx_busy_rise_initializes_counters: assert property (
        @(posedge sys_clk) disable iff (sys_rst) (rx_busy && !$past(rx_busy)) |-> (rx_count16 == 4'd13 && rx_bitcount == 4'd0)
    );
    // Falling rx_busy occurs only on a sample when either bad startbit or final bit reached.
    rx_busy_fall_only_on_sample_events: assert property (
        @(posedge sys_clk) disable iff (sys_rst)
            (!rx_busy && $past(rx_busy)) |-> $past(enable16 && (rx_count16 == 4'd0) &&
                                                  ((rx_bitcount == 4'd0 && !rx2) || (rx_bitcount == 4'd14)))
    );
    // While busy, rx_count16 increments by 1 on each enable16.
    rx_count16_increments_when_busy: assert property (
        @(posedge sys_clk) disable iff (sys_rst) $past(rx_busy) && $past(enable16) |-> (rx_count16 == $past(rx_count16) + 4'd1)
    );
    // On each sample while busy, rx_bitcount increments by 1.
    rx_bitcount_increments_on_sample: assert property (
        @(posedge sys_clk) disable iff (sys_rst) $past(rx_busy) && $past(enable16) && $past(rx_count16 == 4'd0)
            |-> (rx_bitcount == $past(rx_bitcount) + 4'd1)
    );
    // Shift register updates on data-bit samples (excluding start and final bit).
    rx_shift_reg_updates_on_data_bits: assert property (
        @(posedge sys_clk) disable iff (sys_rst)
            $past(rx_busy) && $past(enable16) && $past(rx_count16 == 4'd0) &&
            $past(rx_bitcount != 4'd0) && $past(rx_bitcount != 4'd14)
            |-> (rx_reg == { $past(rx_reg[11:0]), $past(rx2) })
    );

    ///// IRQ and data latch /////
    // rx_irq only asserts after a sample of the final bit while previously busy.
    rx_irq_only_on_final_sample: assert property (
        @(posedge sys_clk) disable iff (sys_rst)
            rx_irq |-> $past(enable16 && rx_busy && rx_count16 == 4'd0 && rx_bitcount == 4'd14)
    );
    // rx_irq is a single-cycle pulse.
    rx_irq_one_cycle: assert property (
        @(posedge sys_clk) disable iff (sys_rst) rx_irq |-> ##1 !rx_irq
    );
    // When rx_irq asserts, rx_busy is cleared in the same cycle.
    rx_irq_clears_busy: assert property (
        @(posedge sys_clk) disable iff (sys_rst) rx_irq |-> !rx_busy
    );
    // When rx_irq asserts, rx_data latches the previous rx_reg value.
    rx_data_latches_on_irq: assert property (
        @(posedge sys_clk) disable iff (sys_rst) rx_irq |-> (rx_data == $past(rx_reg))
    );

    ///// CSR read data mux /////
    // csr_selected matches its decode expression.
    csr_selected_definition: assert property (
        @(posedge sys_clk) disable iff (sys_rst) (csr_selected == (csr_a[13:10] == csr_addr))
    );
    // When not selected in the previous cycle, csr_do is zero.
    csr_do_zero_when_not_selected: assert property (
        @(posedge sys_clk) disable iff (sys_rst) !$past(csr_selected) |-> (csr_do == 32'd0)
    );
    // When selected in the previous cycle, csr_do reflects rx_data (zero-extended).
    csr_do_matches_rx_data_when_selected: assert property (
        @(posedge sys_clk) disable iff (sys_rst) $past(csr_selected)
            |-> (csr_do[12:0] == $past(rx_data) && csr_do[31:13] == 19'd0)
    );

endmodule