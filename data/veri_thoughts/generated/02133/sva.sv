module data_adapter_sva (
    input logic              clk,
    input logic              reset_n,
    input logic              in_ready,
    input logic              in_valid,
    input logic      [ 7: 0] in_data,
    input logic      [ 7: 0] in_channel,
    input logic              in_startofpacket,
    input logic              in_endofpacket,
    input logic              out_ready,
    input logic              out_valid,
    input logic      [ 7: 0] out_data,
    input logic              out_startofpacket,
    input logic              out_endofpacket
);
    // Clock: clk; Reset: reset_n (active-low). Logic: combinational.
    // Behavior: in_ready=out_ready; data/SOP/EOP pass-through; out_valid=in_valid && (in_channel<=15).

    localparam logic [7:0] MAX_CHANNEL = 8'd15;

    // Backpressure passthrough: in_ready mirrors out_ready.
    check_in_ready_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) in_ready == out_ready
    );

    // Data payload passes through unchanged.
    check_data_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) out_data == in_data
    );

    // Start-of-packet passes through unchanged.
    check_sop_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) out_startofpacket == in_startofpacket
    );

    // End-of-packet passes through unchanged.
    check_eop_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) out_endofpacket == in_endofpacket
    );

    // out_valid equals in_valid when channel <= MAX; otherwise 0.
    check_out_valid_definition: assert property (
        @(posedge clk) disable iff (!reset_n) out_valid == (in_valid && (in_channel <= MAX_CHANNEL))
    );

    // Outputs remain stable if all inputs remain stable (purely combinational mapping).
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (!reset_n)
            $stable({in_valid, in_data, in_channel, in_startofpacket, in_endofpacket, out_ready})
            |-> $stable({in_ready, out_valid, out_data, out_startofpacket, out_endofpacket})
    );

    // out_valid is independent of out_ready (since not used in its computation).
    check_out_valid_independent_of_out_ready: assert property (
        @(posedge clk) disable iff (!reset_n)
            $stable({in_valid, in_channel}) && $changed(out_ready)
            |-> $stable(out_valid)
    );

    // out_valid is independent of payload/SOP/EOP (since not used in its computation).
    check_out_valid_independent_of_payload_ctrl: assert property (
        @(posedge clk) disable iff (!reset_n)
            $stable({in_valid, in_channel}) && $changed({in_data, in_startofpacket, in_endofpacket})
            |-> $stable(out_valid)
    );

    // When channel is in range for two cycles, a rising in_valid causes a rising out_valid.
    check_out_valid_rise_tracks_in_valid: assert property (
        @(posedge clk) disable iff (!reset_n)
            $rose(in_valid) && (in_channel <= MAX_CHANNEL) && $past(in_channel <= MAX_CHANNEL)
            |-> $rose(out_valid)
    );

    // When channel is in range for two cycles, a falling in_valid causes a falling out_valid.
    check_out_valid_fall_tracks_in_valid: assert property (
        @(posedge clk) disable iff (!reset_n)
            $fell(in_valid) && (in_channel <= MAX_CHANNEL) && $past(in_channel <= MAX_CHANNEL)
            |-> $fell(out_valid)
    );

endmodule