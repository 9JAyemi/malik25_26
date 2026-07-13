module soc_system_hps_only_master_b2p_adapter_sva (
    input logic       clk,
    input logic       reset_n,
    input logic       in_ready,
    input logic       in_valid,
    input logic [7:0] in_data,
    input logic [7:0] in_channel,
    input logic       in_startofpacket,
    input logic       in_endofpacket,
    input logic       out_ready,
    input logic       out_valid,
    input logic [7:0] out_data,
    input logic       out_startofpacket,
    input logic       out_endofpacket
);

    // in_ready directly mirrors out_ready.
    check_in_ready_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n)
        (in_ready == out_ready)
    );

    // out_data directly mirrors in_data.
    check_out_data_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n)
        (out_data == in_data)
    );

    // out_startofpacket directly mirrors in_startofpacket.
    check_out_startofpacket_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n)
        (out_startofpacket == in_startofpacket)
    );

    // out_endofpacket directly mirrors in_endofpacket.
    check_out_endofpacket_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n)
        (out_endofpacket == in_endofpacket)
    );

    // Channel 0 passes in_valid through to out_valid.
    check_out_valid_passthrough_channel_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (in_channel == 8'h00) |-> (out_valid == in_valid)
    );

    // Nonzero channels force out_valid low.
    check_out_valid_blocked_nonzero_channel: assert property (
        @(posedge clk) disable iff (!reset_n)
        (in_channel > 8'h00) |-> (out_valid == 1'b0)
    );

endmodule