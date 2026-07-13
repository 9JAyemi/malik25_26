module lab3_master_0_b2p_adapter_sva (
    input  logic         clk,
    input  logic         reset_n,
    input  logic         in_ready,
    input  logic         in_valid,
    input  logic  [7:0]  in_data,
    input  logic  [7:0]  in_channel,
    input  logic         in_startofpacket,
    input  logic         in_endofpacket,
    input  logic         out_ready,
    input  logic         out_valid,
    input  logic  [7:0]  out_data,
    input  logic         out_startofpacket,
    input  logic         out_endofpacket
);

    // in_ready is a combinational passthrough of out_ready
    check_in_ready_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) in_ready == out_ready
    );

    // out_data is a combinational passthrough of in_data
    check_out_data_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) out_data == in_data
    );

    // out_startofpacket is a combinational passthrough of in_startofpacket
    check_out_sop_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) out_startofpacket == in_startofpacket
    );

    // out_endofpacket is a combinational passthrough of in_endofpacket
    check_out_eop_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) out_endofpacket == in_endofpacket
    );

    // When in_channel > 0, out_valid is forced LOW
    check_out_valid_block_when_channel_gt0: assert property (
        @(posedge clk) disable iff (!reset_n) (in_channel > 8'd0) |-> (out_valid == 1'b0)
    );

    // When in_channel == 0, out_valid follows in_valid
    check_out_valid_follow_when_channel_0: assert property (
        @(posedge clk) disable iff (!reset_n) (in_channel == 8'd0) |-> (out_valid == in_valid)
    );

    // If out_valid is HIGH, then in_channel must be 0 and in_valid must be HIGH
    check_out_valid_high_implies_inputs: assert property (
        @(posedge clk) disable iff (!reset_n) out_valid |-> ((in_channel == 8'd0) && (in_valid == 1'b1))
    );

    // If in_channel == 0 and in_valid is HIGH, out_valid must be HIGH
    check_out_valid_high_when_allowed: assert property (
        @(posedge clk) disable iff (!reset_n) ((in_channel == 8'd0) && (in_valid == 1'b1)) |-> (out_valid == 1'b1)
    );

    // If in_channel == 0 and in_valid is LOW, out_valid must be LOW
    check_out_valid_low_when_not_valid: assert property (
        @(posedge clk) disable iff (!reset_n) ((in_channel == 8'd0) && (in_valid == 1'b0)) |-> (out_valid == 1'b0)
    );

endmodule