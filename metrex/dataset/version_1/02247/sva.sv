// SVA for receiver and synchronizer_1bit
// Concise checks and coverage; bind to DUTs

// Receiver SVA
module receiver_sva #(parameter DATA_BITS=32)
(
  input clk, rst,
  input stb,
  input [DATA_BITS-1:0] data,
  input [DATA_BITS-1:0] data_out,
  input ack, valid,
  input stb_selected // internal synchronized strobe
);
  default clocking cb @(posedge clk); endclocking

  // Reset effects (next cycle)
  ap_rst_clears: assert property (rst |=> (data_out=='0 && !ack && !valid));

  // Handshake ordering and stickiness
  ap_ack_on_stb:              assert property (disable iff (rst) stb_selected |=> ack);
  ap_valid_after_ack:         assert property (disable iff (rst) $rose(ack) |=> valid);
  ap_valid_implies_ack:       assert property (disable iff (rst) valid |-> ack);
  ap_ack_rise_requires_stb:   assert property (disable iff (rst) $rose(ack)   |-> $past(stb_selected));
  ap_valid_rise_req_ack:      assert property (disable iff (rst) $rose(valid) |-> $past(ack));
  ap_ack_sticky:              assert property (disable iff (rst) ack   |=> ack);
  ap_valid_sticky:            assert property (disable iff (rst) valid |=> valid);

  // Data capture semantics
  ap_data_capture:            assert property (disable iff (rst) stb_selected |=> (data_out == $past(data)));
  ap_data_change_only_on_stb: assert property (disable iff (rst) $changed(data_out) |-> $past(stb_selected));

  // Coverage
  cp_basic_handshake: cover property (disable iff (rst) $rose(stb_selected) ##1 ack ##1 valid);
  cp_two_strobes:     cover property (disable iff (rst)
                                      $rose(stb_selected) ##1 (data_out == $past(data)) ##1
                                      $rose(stb_selected) ##1 (data_out == $past(data)));
  cp_strobe_after_ack: cover property (disable iff (rst)
                                       ack ##1 $rose(stb_selected) ##1 (data_out == $past(data)));
endmodule

// Synchronizer SVA
module synchronizer_1bit_sva (input clk, rst, in, out);
  default clocking cb @(posedge clk); endclocking

  ap_sync_rst_clears: assert property (rst |=> (out==1'b0));
  // After 2 cycles out of reset, out must be in delayed by 2 cycles
  ap_two_cycle_latency: assert property ((!rst && !$past(rst) && !$past(rst,2)) |-> (out == $past(in,2)));

  // Coverage: observe a transfer through the 2-flop chain
  cp_sync_transfer: cover property (disable iff (rst) $changed(in) ##2 $changed(out));
endmodule

// Binds
bind receiver         receiver_sva        #(.DATA_BITS(DATA_BITS))
  u_receiver_sva (.clk(clk), .rst(rst), .stb(stb), .data(data), .data_out(data_out), .ack(ack), .valid(valid), .stb_selected(stb_selected));

bind synchronizer_1bit synchronizer_1bit_sva
  u_sync_sva (.clk(clk), .rst(rst), .in(in), .out(out));