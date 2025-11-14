// SVA for Computer_System_Video_In_Subsystem_Edge_Detection_Subsystem_Video_Stream_Merger
// Bind into the DUT for in-scope access to internal signals
module Computer_System_Video_In_Subsystem_Edge_Detection_Subsystem_Video_Stream_Merger_sva
  #(parameter DW=23, EW=1)
(
  input clk, reset,

  input sync_data, sync_valid,
  input [DW:0] stream_in_data_0,
  input        stream_in_startofpacket_0,
  input        stream_in_endofpacket_0,
  input [EW:0] stream_in_empty_0,
  input        stream_in_valid_0,

  input [DW:0] stream_in_data_1,
  input        stream_in_startofpacket_1,
  input        stream_in_endofpacket_1,
  input [EW:0] stream_in_empty_1,
  input        stream_in_valid_1,

  input        stream_out_ready,

  input        sync_ready,

  input        stream_in_ready_0,
  input        stream_in_ready_1,

  input [DW:0] stream_out_data,
  input        stream_out_startofpacket,
  input        stream_out_endofpacket,
  input [EW:0] stream_out_empty,
  input        stream_out_valid,

  // internal DUT signals
  input        enable_setting_stream_select,
  input        between_frames,
  input        stream_select_reg
);

default clocking cb @(posedge clk); endclocking
default disable iff (reset)

// Reset effects
assert property (@(posedge clk) reset |=> (stream_out_valid==0 &&
                                          stream_out_startofpacket==0 &&
                                          stream_out_endofpacket==0 &&
                                          stream_out_data=='0 &&
                                          stream_out_empty=='0));
assert property (@(posedge clk) reset |=> (between_frames==1 && stream_select_reg==0));

// Ready mux equations and mutual exclusion
assert property (!stream_select_reg |-> (stream_in_ready_0 == (stream_in_valid_0 && (!stream_out_valid || stream_out_ready)) &&
                                         stream_in_ready_1 == 1'b0));
assert property ( stream_select_reg |-> (stream_in_ready_1 == (stream_in_valid_1 && (!stream_out_valid || stream_out_ready)) &&
                                         stream_in_ready_0 == 1'b0));
assert property (!(stream_in_ready_0 && stream_in_ready_1));

// Backpressure blocks acceptance
assert property (stream_out_valid && !stream_out_ready |-> !stream_in_ready_0 && !stream_in_ready_1);

// Acceptance updates outputs on next cycle (stream 0)
assert property (stream_in_ready_0 |=> (stream_out_valid          == $past(stream_in_valid_0) &&
                                        stream_out_startofpacket  == $past(stream_in_startofpacket_0) &&
                                        stream_out_endofpacket    == $past(stream_in_endofpacket_0) &&
                                        stream_out_empty          == $past(stream_in_empty_0) &&
                                        stream_out_data           == $past(stream_in_data_0)));
// Acceptance updates outputs on next cycle (stream 1)
assert property (stream_in_ready_1 |=> (stream_out_valid          == $past(stream_in_valid_1) &&
                                        stream_out_startofpacket  == $past(stream_in_startofpacket_1) &&
                                        stream_out_endofpacket    == $past(stream_in_endofpacket_1) &&
                                        stream_out_empty          == $past(stream_in_empty_1) &&
                                        stream_out_data           == $past(stream_in_data_1)));

// No acceptance: clear on consumer ready, hold otherwise
assert property (!stream_in_ready_0 && !stream_in_ready_1 && stream_out_ready |=> stream_out_valid==0);
assert property (!stream_in_ready_0 && !stream_in_ready_1 && !stream_out_ready |=> ($stable(stream_out_valid) &&
                                                                                    $stable(stream_out_data) &&
                                                                                    $stable(stream_out_startofpacket) &&
                                                                                    $stable(stream_out_endofpacket) &&
                                                                                    $stable(stream_out_empty)));

// between_frames state machine
assert property ((stream_in_ready_0 && stream_in_startofpacket_0) ||
                 (stream_in_ready_1 && stream_in_startofpacket_1) |=> between_frames==0);
assert property ((stream_in_ready_0 && stream_in_endofpacket_0)   ||
                 (stream_in_ready_1 && stream_in_endofpacket_1)   |=> between_frames==1);

// Enable select setting semantics
assert property (between_frames |-> enable_setting_stream_select); // always enabled between frames
assert property (!between_frames |-> (enable_setting_stream_select ==
                                     ((stream_in_ready_0 && stream_in_endofpacket_0) ||
                                      (stream_in_ready_1 && stream_in_endofpacket_1))));
assert property (sync_ready == enable_setting_stream_select);

// stream_select_reg update protocol
assert property (enable_setting_stream_select && sync_valid |=> stream_select_reg == $past(sync_data));
assert property (!(enable_setting_stream_select && sync_valid) |=> $stable(stream_select_reg));
assert property ($changed(stream_select_reg) |-> $past(enable_setting_stream_select && sync_valid));

// Coverage
cover property (stream_in_ready_0 && stream_in_startofpacket_0 ##[1:$] stream_in_ready_0 && stream_in_endofpacket_0);
cover property (stream_in_ready_1 && stream_in_startofpacket_1 ##[1:$] stream_in_ready_1 && stream_in_endofpacket_1);
cover property (between_frames && enable_setting_stream_select && sync_valid && (sync_data==1'b1) ##1 stream_select_reg==1'b1);
cover property (between_frames && enable_setting_stream_select && sync_valid && (sync_data==1'b0) ##1 stream_select_reg==1'b0);
cover property (stream_out_valid && !stream_out_ready ##1 !stream_in_ready_0 && !stream_in_ready_1);

endmodule

bind Computer_System_Video_In_Subsystem_Edge_Detection_Subsystem_Video_Stream_Merger
  Computer_System_Video_In_Subsystem_Edge_Detection_Subsystem_Video_Stream_Merger_sva
    #(.DW(DW), .EW(EW))
    sva_i (.*);