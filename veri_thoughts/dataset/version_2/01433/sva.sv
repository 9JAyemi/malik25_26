module SerialRX_sva (
    input logic clk,
    input logic RxD,
    input logic RxD_data_ready,
    input logic [7:0] RxD_data,
    input logic RxD_endofpacket,
    input logic RxD_idle
);
    // Clock: clk (posedge). No reset in RTL. Mixed logic (sequential regs; RxD_idle is combinational from a counter).

    // End-of-packet implies entering idle now and was not idle in the previous cycle.
    check_eop_implies_idle_and_prev_not_idle: assert property (
        @(posedge clk) RxD_endofpacket |-> (RxD_idle && !$past(RxD_idle,1,1'b0))
    );

    // Idle rising edge only occurs together with end-of-packet.
    check_idle_rise_implies_eop: assert property (
        @(posedge clk) (!$past(RxD_idle,1,1'b0) && RxD_idle) |-> RxD_endofpacket
    );

    // End-of-packet is a single-cycle pulse (no back-to-back 1s).
    check_eop_one_cycle_pulse: assert property (
        @(posedge clk) $past(RxD_endofpacket,1,1'b0) |-> !RxD_endofpacket
    );

    // Data-ready is a single-cycle pulse (no back-to-back 1s).
    check_data_ready_one_cycle_pulse: assert property (
        @(posedge clk) $past(RxD_data_ready,1,1'b0) |-> !RxD_data_ready
    );

    // When idle, data-ready must be low.
    check_idle_excludes_data_ready: assert property (
        @(posedge clk) RxD_idle |-> !RxD_data_ready
    );

    // When data-ready is high, idle must be low.
    check_data_ready_excludes_idle: assert property (
        @(posedge clk) RxD_data_ready |-> !RxD_idle
    );

    // When data-ready is high, end-of-packet must be low.
    check_data_ready_excludes_eop: assert property (
        @(posedge clk) RxD_data_ready |-> !RxD_endofpacket
    );

    // While staying idle (not the first idle cycle), end-of-packet cannot assert.
    check_idle_steady_no_eop: assert property (
        @(posedge clk) (RxD_idle && $past(RxD_idle,1,1'b0)) |-> !RxD_endofpacket
    );

    // Idle falling edge cannot coincide with end-of-packet or data-ready.
    check_idle_fall_excludes_eop_and_data_ready: assert property (
        @(posedge clk) ($past(RxD_idle,1,1'b0) && !RxD_idle) |-> (!RxD_endofpacket && !RxD_data_ready)
    );

    // Data bus is stable on the cycle data-ready is asserted.
    check_data_stable_on_ready: assert property (
        @(posedge clk) RxD_data_ready |-> (RxD_data == $past(RxD_data,1,RxD_data))
    );

    // Data bus remains stable during idle cycles.
    check_data_stable_while_idle: assert property (
        @(posedge clk) RxD_idle |-> (RxD_data == $past(RxD_data,1,RxD_data))
    );
endmodule