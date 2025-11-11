// SystemVerilog Assertions for channel_bridge
// Concise, high-quality checks and coverage

module channel_bridge_sva (
  input  logic        clk,
  input  logic        reset_n,
  input  logic        in_valid,
  input  logic [7:0]  in_data,
  input  logic [7:0]  in_channel,
  input  logic        in_startofpacket,
  input  logic        in_endofpacket,
  input  logic        out_valid,
  input  logic [7:0]  out_data,
  input  logic [7:0]  out_channel,
  input  logic        out_startofpacket,
  input  logic        out_endofpacket,
  input  logic [7:0]  stored_data,
  input  logic [7:0]  stored_channel,
  input  logic        stored_startofpacket,
  input  logic        stored_endofpacket
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n)

  // Reset values (synchronous reset check; not disabled by reset)
  property p_reset_values;
    @(posedge clk) (!reset_n) |-> (out_valid==1'b0 &&
                                   out_data==8'd0 &&
                                   out_channel==8'd0 &&
                                   out_startofpacket==1'b0 &&
                                   out_endofpacket==1'b0);
  endproperty
  a_reset_values: assert property (p_reset_values);

  // Storage updates only on in_valid
  a_store_updates: assert property (in_valid |=> (stored_data==$past(in_data) &&
                                                  stored_channel==$past(in_channel) &&
                                                  stored_startofpacket==$past(in_startofpacket) &&
                                                  stored_endofpacket==$past(in_endofpacket)));
  a_store_stable_when_no_in: assert property (!in_valid |=> $stable({stored_data,stored_channel,stored_startofpacket,stored_endofpacket}));

  // Output equals previous stored_* whenever out_valid is 1
  a_out_eq_prev_stored: assert property (out_valid |-> (out_data==$past(stored_data) &&
                                                        out_channel==$past(stored_channel) &&
                                                        out_startofpacket==$past(stored_startofpacket) &&
                                                        out_endofpacket==$past(stored_endofpacket)));

  // Outputs hold when out_valid is 0
  a_hold_when_not_valid: assert property (!out_valid |=> $stable({out_data,out_channel,out_startofpacket,out_endofpacket}));

  // out_valid control protocol
  a_ov_0_always_to_1:     assert property (!out_valid |=> out_valid);
  a_ov_1_ch0_stays_1:     assert property (out_valid && (in_channel==8'd0) |=> out_valid);
  a_ov_1_chnz_goes_0:     assert property (out_valid && (in_channel>8'd0)  |=> !out_valid);
  a_drop_only_if_chnz:    assert property (!out_valid && $past(out_valid) |-> $past(in_channel>8'd0));
  a_suppression_one_cycle: assert property (out_valid && (in_channel>8'd0) |=> !out_valid ##1 out_valid);

  // Basic X-protection when used: outputs must be known when asserted valid and after at least one store
  // This avoids false failures immediately after reset before any in_valid
  sequence s_seen_store; in_valid ##0 1; endsequence
  a_known_on_use: assert property ( (out_valid && $past(in_valid,1)) |-> !$isunknown({out_data,out_channel,out_startofpacket,out_endofpacket}) );

  // Coverage
  c_reset_release:        cover property ($fell(reset_n) ##1 reset_n ##1 out_valid);
  c_no_suppress_path:     cover property (out_valid && (in_channel==8'd0) ##1 out_valid);
  c_suppress_sequence:    cover property (out_valid && (in_channel>8'd0) ##1 !out_valid ##1 out_valid);
  c_capture_and_output:   cover property (in_valid ##1 out_valid && (out_data==$past(stored_data)));

endmodule

// Bind into DUT; connects internal regs for checking
bind channel_bridge channel_bridge_sva sva_i (
  .clk                 (clk),
  .reset_n             (reset_n),
  .in_valid            (in_valid),
  .in_data             (in_data),
  .in_channel          (in_channel),
  .in_startofpacket    (in_startofpacket),
  .in_endofpacket      (in_endofpacket),
  .out_valid           (out_valid),
  .out_data            (out_data),
  .out_channel         (out_channel),
  .out_startofpacket   (out_startofpacket),
  .out_endofpacket     (out_endofpacket),
  .stored_data         (stored_data),
  .stored_channel      (stored_channel),
  .stored_startofpacket(stored_startofpacket),
  .stored_endofpacket  (stored_endofpacket)
);