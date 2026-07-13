module ip_packet_filter_sva (
    input logic clk,
    input logic rst,
    input logic input_ip_hdr_valid,
    input logic input_ip_hdr_ready,
    input logic [31:0] input_ip_dest_ip,
    input logic output_ip_hdr_valid,
    input logic output_ip_hdr_ready,
    input logic [31:0] output_ip_dest_ip,
    input logic [47:0] output_ip_eth_dest_mac,
    input logic [15:0] output_ip_length,
    input logic drop
);
    // Clock: clk; Reset: rst (sync, active-high).
    // Logic: mixed (combinational assigns + sequential regs).
    // Key behavior: ready=1, valid mirrors input; on (input_ip_hdr_valid & output_ip_hdr_ready) capture dest_ip and set drop=(input_ip_dest_ip==FILTER_IP); eth_mac/length remain constant after reset.

    localparam logic [31:0] FILTER_IP = 32'hc0a80101;

    // input_ip_hdr_ready is hard-wired HIGH.
    check_input_ready_const_high: assert property (
        @(posedge clk) disable iff (rst) input_ip_hdr_ready == 1'b1
    );

    // output_ip_hdr_valid mirrors input_ip_hdr_valid.
    check_valid_passthrough: assert property (
        @(posedge clk) disable iff (rst) output_ip_hdr_valid == input_ip_hdr_valid
    );

    // Synchronous reset drives outputs to zero on the next cycle.
    check_reset_clears_outputs: assert property (
        @(posedge clk) rst |=> (output_ip_dest_ip == 32'h0) && (output_ip_eth_dest_mac == 48'h0) && (output_ip_length == 16'h0) && (drop == 1'b0)
    );

    // On handshake, capture input_ip_dest_ip into output_ip_dest_ip on next cycle.
    check_capture_dest_ip_on_handshake: assert property (
        @(posedge clk) disable iff (rst)
            (input_ip_hdr_valid && output_ip_hdr_ready) |=> (output_ip_dest_ip == $past(input_ip_dest_ip, 1, rst))
    );

    // Without handshake, output_ip_dest_ip holds its value.
    check_dest_ip_stable_without_handshake: assert property (
        @(posedge clk) disable iff (rst)
            !(input_ip_hdr_valid && output_ip_hdr_ready) |=> (output_ip_dest_ip == $past(output_ip_dest_ip, 1, rst))
    );

    // On handshake, drop updates to (input_ip_dest_ip == FILTER_IP) on next cycle.
    check_drop_update_on_handshake: assert property (
        @(posedge clk) disable iff (rst)
            (input_ip_hdr_valid && output_ip_hdr_ready) |=> (drop == ($past(input_ip_dest_ip, 1, rst) == FILTER_IP))
    );

    // Without handshake, drop holds its value.
    check_drop_stable_without_handshake: assert property (
        @(posedge clk) disable iff (rst)
            !(input_ip_hdr_valid && output_ip_hdr_ready) |=> (drop == $past(drop, 1, rst))
    );

    // Any change in drop must be due to a handshake in the prior cycle and must match the compare result.
    check_drop_change_requires_prev_handshake: assert property (
        @(posedge clk) disable iff (rst)
            (drop != $past(drop, 1, rst)) |-> $past(input_ip_hdr_valid && output_ip_hdr_ready, 1, rst)
                                         && (drop == ($past(input_ip_dest_ip, 1, rst) == FILTER_IP))
    );

    // Any change in output_ip_dest_ip must be due to a handshake in the prior cycle and must match the input sampled then.
    check_dest_ip_change_requires_prev_handshake: assert property (
        @(posedge clk) disable iff (rst)
            (output_ip_dest_ip != $past(output_ip_dest_ip, 1, rst)) |-> $past(input_ip_hdr_valid && output_ip_hdr_ready, 1, rst)
                                                                   && (output_ip_dest_ip == $past(input_ip_dest_ip, 1, rst))
    );

    // output_ip_eth_dest_mac remains constant after reset (self-assignment in RTL).
    check_eth_mac_stable_post_reset: assert property (
        @(posedge clk) disable iff (rst) $stable(output_ip_eth_dest_mac)
    );

    // output_ip_length remains constant after reset (self-assignment in RTL).
    check_length_stable_post_reset: assert property (
        @(posedge clk) disable iff (rst) $stable(output_ip_length)
    );

endmodule