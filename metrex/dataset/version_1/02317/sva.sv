// SVA for FrameWriter
// Recommended usage:
//   bind FrameWriter FrameWriter_SVA #(.DATA_WIDTH(DATA_WIDTH),
//                                      .FIFO_DEPTH(FIFO_DEPTH),
//                                      .FIFO_DEPTH_LOG2(FIFO_DEPTH_LOG2)) u_fw_sva (
//      .clk(clk), .rst(rst),
//      .din_data(din_data), .din_valid(din_valid), .din_sop(din_sop), .din_eop(din_eop),
//      .data_fifo_out(data_fifo_out), .data_valid_fifo_out(data_valid_fifo_out),
//      .usedw_fifo_out(usedw_fifo_out), .din_ready(din_ready),
//      .start(start), .endf(endf),
//      .video_reg(video_reg), .run(run), .set_video(set_video), .reset_video(reset_video)
//   );

module FrameWriter_SVA #(parameter int DATA_WIDTH = 32,
                         parameter int FIFO_DEPTH = 256,
                         parameter int FIFO_DEPTH_LOG2 = 8)
(
  input  logic                     clk,
  input  logic                     rst,

  input  logic [23:0]              din_data,
  input  logic                     din_valid,
  input  logic                     din_sop,
  input  logic                     din_eop,

  input  logic [DATA_WIDTH-1:0]    data_fifo_out,
  input  logic                     data_valid_fifo_out,
  input  logic [FIFO_DEPTH_LOG2:0] usedw_fifo_out,
  input  logic                     din_ready,

  input  logic                     start,
  input  logic                     endf,

  // internal DUT signals
  input  logic                     video_reg,
  input  logic [1:0]               run,
  input  logic                     set_video,
  input  logic                     reset_video
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Combinational equivalences
  assert property (endf == (run == 2));
  assert property (data_fifo_out == {8'h00, din_data});
  assert property (data_valid_fifo_out == (video_reg && din_valid && (run == 1)));
  assert property (din_ready == (usedw_fifo_out < (FIFO_DEPTH - 1)));

  // State/encoding checks
  assert property (run inside {2'd0,2'd1,2'd2});
  // Async reset drives run=0
  assert property (@(posedge rst) run == 2'd0);

  // Run FSM transitions
  assert property (start |=> run == 2'd1);
  assert property ((reset_video && !start) |=> run == 2'd2);
  assert property (endf |=> run == 2'd0);
  assert property ((run == 2'd2) |=> run == 2'd0); // state 2 is one-cycle

  // Video flag behavior and priorities
  assert property ($rose(video_reg) |-> (!start && set_video));
  assert property ($fell(video_reg) |-> (start || (reset_video && !set_video)));
  assert property (video_reg |-> (run == 1));
  // Sanity on set/reset definitions (glitch/typo catcher)
  assert property (set_video |-> (din_sop && din_valid && din_data == 24'h0 && run == 1));
  assert property (reset_video |-> (din_eop && din_valid && video_reg));
  // If set and reset coincide (single-beat), set dominates per RTL
  assert property ((set_video && reset_video && !start) |-> $rose(video_reg));

  // Ready boundary behavior
  assert property ((usedw_fifo_out == (FIFO_DEPTH - 1)) |-> !din_ready);
  assert property ((usedw_fifo_out <= (FIFO_DEPTH - 2)) |-> din_ready);

  // Interactions with start
  assert property (start |-> !data_valid_fifo_out); // start forces video_reg=0 that cycle

  // Coverage
  sequence s_full_frame;
    start ##1 set_video ##[1:$] reset_video ##1 endf;
  endsequence
  cover property (s_full_frame);

  cover property (set_video && reset_video); // single-beat frame (SOP=EOP same cycle)

  cover property ((usedw_fifo_out == (FIFO_DEPTH - 2)) ##1 (usedw_fifo_out == (FIFO_DEPTH - 1)));
  cover property ((usedw_fifo_out == (FIFO_DEPTH - 1)) ##1 (usedw_fifo_out == (FIFO_DEPTH - 2)));

  cover property (start ##1 (run == 1) ##[1:$] (run == 2) ##1 (run == 0));

endmodule