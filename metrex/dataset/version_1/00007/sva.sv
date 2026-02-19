module async_transmitter_sva (
    input logic clk,
    input logic TxD_start,
    input logic [7:0] TxD_data,
    input logic TxD,
    input logic TxD_busy
);

    ///// Transmitter invariants and sequencing /////
    // When idle (not busy), the line must be HIGH (mark level).
    check_txd_idle_high: assert property (
        @(posedge clk) (!TxD_busy) |-> (TxD == 1'b1)
    );

    // If idle and no start request, remain idle on the next cycle.
    check_txd_idle_stable_without_start: assert property (
        @(posedge clk) (!TxD_busy && !TxD_start) |-> ##1 (!TxD_busy)
    );

    // If idle and a start request occurs, transmitter becomes busy on the next cycle.
    check_txd_start_sets_busy_next: assert property (
        @(posedge clk) (!TxD_busy && TxD_start) |-> ##1 (TxD_busy)
    );

    // Busy can only rise as a result of a start request in that cycle.
    check_txd_busy_rise_requires_start: assert property (
        @(posedge clk) $rose(TxD_busy) |-> (TxD_start == 1'b1)
    );

    // At time 0 (initial state), the transmitter is idle and line is HIGH.
    check_txd_init_idle_high: assert property (
        @(posedge clk) $initstate |-> (!TxD_busy && (TxD == 1'b1))
    );

endmodule



module async_receiver_sva (
    input logic clk,
    input logic RxD,
    input logic RxD_data_ready,
    input logic [7:0] RxD_data,
    input logic RxD_idle,
    input logic RxD_endofpacket
);

    ///// Receiver invariants and pulse shaping /////
    // RxD_idle and RxD_endofpacket cannot be HIGH at the same time.
    check_rxd_idle_eop_mutex: assert property (
        @(posedge clk) !(RxD_idle && RxD_endofpacket)
    );

    // When a byte is reported ready, receiver is not idle in that cycle.
    check_rxd_dr_idle_mutex: assert property (
        @(posedge clk) RxD_data_ready |-> !RxD_idle
    );

    // When a byte is reported ready, end-of-packet is not asserted in that cycle.
    check_rxd_dr_eop_mutex: assert property (
        @(posedge clk) RxD_data_ready |-> !RxD_endofpacket
    );

    // RxD_data_ready is a single-cycle pulse.
    check_rxd_dr_single_pulse: assert property (
        @(posedge clk) RxD_data_ready |-> ##1 !RxD_data_ready
    );

    // RxD_endofpacket is a single-cycle pulse.
    check_rxd_eop_single_pulse: assert property (
        @(posedge clk) RxD_endofpacket |-> ##1 !RxD_endofpacket
    );

    // After a data_ready pulse, the reported data remains stable on the next cycle.
    check_rxd_data_stable_after_ready: assert property (
        @(posedge clk) RxD_data_ready |-> ##1 $stable(RxD_data)
    );

    // At time 0 (initial state), data_ready and endofpacket are LOW, and idle is LOW.
    check_rxd_init_flags_low: assert property (
        @(posedge clk) $initstate |-> (!RxD_data_ready && !RxD_endofpacket && (RxD_idle == 1'b0))
    );

endmodule