module soc_system_master_secure_b2p_adapter_sva (
    input  logic             clk,
    input  logic             reset_n,
    input  logic             in_ready,
    input  logic             in_valid,
    input  logic [7:0]       in_data,
    input  logic [7:0]       in_channel,
    input  logic             in_startofpacket,
    input  logic             in_endofpacket,
    input  logic             out_ready,
    input  logic             out_valid,
    input  logic [7:0]       out_data,
    input  logic             out_startofpacket,
    input  logic             out_endofpacket
);
    // Clock: clk; Reset: reset_n (active-low). Logic is combinational pass-through with out_valid masked when in_channel > 8'h0F.

    // in_ready is a direct pass-through of out_ready.
    check_in_ready_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) (in_ready == out_ready)
    );

    // out_data matches in_data every cycle.
    check_out_data_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) (out_data == in_data)
    );

    // out_startofpacket matches in_startofpacket every cycle.
    check_out_sop_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) (out_startofpacket == in_startofpacket)
    );

    // out_endofpacket matches in_endofpacket every cycle.
    check_out_eop_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) (out_endofpacket == in_endofpacket)
    );

    // out_valid is deasserted when in_channel > 8'h0F.
    check_valid_masked_when_channel_high: assert property (
        @(posedge clk) disable iff (!reset_n) (in_channel > 8'h0F) |-> (out_valid == 1'b0)
    );

    // When in_channel <= 8'h0F, out_valid equals in_valid.
    check_valid_follows_input_when_channel_ok: assert property (
        @(posedge clk) disable iff (!reset_n) (in_channel <= 8'h0F) |-> (out_valid == in_valid)
    );

    // out_valid implies in_valid is asserted.
    check_out_valid_implies_in_valid: assert property (
        @(posedge clk) disable iff (!reset_n) out_valid |-> in_valid
    );

    // out_valid implies channel is within range (<= 8'h0F).
    check_out_valid_implies_channel_in_range: assert property (
        @(posedge clk) disable iff (!reset_n) out_valid |-> (in_channel <= 8'h0F)
    );

    // If in_valid is low, out_valid must be low.
    check_in_valid_low_forces_out_valid_low: assert property (
        @(posedge clk) disable iff (!reset_n) (!in_valid) |-> (!out_valid)
    );

    // If input is valid and output is dropped, the channel must be > 8'h0F.
    check_drop_only_due_to_channel: assert property (
        @(posedge clk) disable iff (!reset_n) (in_valid && !out_valid) |-> (in_channel > 8'h0F)
    );

    // out_valid equals (in_valid && (in_channel <= 8'h0F)).
    check_valid_logic_equivalence: assert property (
        @(posedge clk) disable iff (!reset_n) out_valid == (in_valid && (in_channel <= 8'h0F))
    );
endmodule