module fifo36_demux_sva
  #(parameter logic [35:0] match_data = 36'd0,
    parameter logic [35:0] match_mask = 36'd0)
   (input logic        clk,
    input logic        reset,
    input logic        clear,
    input logic [35:0] data_i,
    input logic        src_rdy_i,
    input logic        dst_rdy_o,
    input logic [35:0] data0_o,
    input logic        src0_rdy_o,
    input logic        dst0_rdy_i,
    input logic [35:0] data1_o,
    input logic        src1_rdy_o,
    input logic        dst1_rdy_i,
    input logic [1:0]  state);

   localparam logic [1:0] DMX_IDLE  = 2'd0;
   localparam logic [1:0] DMX_DATA0 = 2'd1;
   localparam logic [1:0] DMX_DATA1 = 2'd2;

   wire match;
   wire eof;

   assign match = |((data_i ^ match_data) & match_mask);
   assign eof   = data_i[33];

   // Reset or clear forces the FSM back to IDLE.
   check_reset_or_clear_forces_idle: assert property (
      @(posedge clk)
      (reset || clear) |=> (state == DMX_IDLE)
   );

   // data0_o is always a direct copy of data_i.
   check_data0_passthrough: assert property (
      @(posedge clk) disable iff (reset || clear)
      (data0_o == data_i)
   );

   // data1_o is always a direct copy of data_i.
   check_data1_passthrough: assert property (
      @(posedge clk) disable iff (reset || clear)
      (data1_o == data_i)
   );

   // IDLE drives no ready signals downstream.
   check_idle_outputs: assert property (
      @(posedge clk) disable iff (reset || clear)
      (state == DMX_IDLE) |-> ((dst_rdy_o == 1'b0) && (src0_rdy_o == 1'b0) && (src1_rdy_o == 1'b0))
   );

   // DATA0 forwards src_rdy_i and dst0_rdy_i on the selected path.
   check_data0_outputs: assert property (
      @(posedge clk) disable iff (reset || clear)
      (state == DMX_DATA0) |-> ((dst_rdy_o == dst0_rdy_i) && (src0_rdy_o == src_rdy_i) && (src1_rdy_o == 1'b0))
   );

   // DATA1 forwards src_rdy_i and dst1_rdy_i on the selected path.
   check_data1_outputs: assert property (
      @(posedge clk) disable iff (reset || clear)
      (state == DMX_DATA1) |-> ((dst_rdy_o == dst1_rdy_i) && (src1_rdy_o == src_rdy_i) && (src0_rdy_o == 1'b0))
   );

   // IDLE selects DATA0 when src_rdy_i is high and the match expression is low.
   check_idle_to_data0: assert property (
      @(posedge clk) disable iff (reset || clear)
      ((state == DMX_IDLE) && src_rdy_i && !match) |=> (state == DMX_DATA0)
   );

   // IDLE selects DATA1 when src_rdy_i is high and the match expression is high.
   check_idle_to_data1: assert property (
      @(posedge clk) disable iff (reset || clear)
      ((state == DMX_IDLE) && src_rdy_i && match) |=> (state == DMX_DATA1)
   );

   // IDLE holds when no source data is ready.
   check_idle_hold_without_src: assert property (
      @(posedge clk) disable iff (reset || clear)
      ((state == DMX_IDLE) && !src_rdy_i) |=> (state == DMX_IDLE)
   );

   // DATA0 returns to IDLE on an accepted EOF beat.
   check_data0_to_idle_on_eof_handshake: assert property (
      @(posedge clk) disable iff (reset || clear)
      ((state == DMX_DATA0) && src_rdy_i && dst0_rdy_i && eof) |=> (state == DMX_IDLE)
   );

   // DATA0 holds until an accepted EOF beat occurs.
   check_data0_hold_without_eof_handshake: assert property (
      @(posedge clk) disable iff (reset || clear)
      ((state == DMX_DATA0) && !(src_rdy_i && dst0_rdy_i && eof)) |=> (state == DMX_DATA0)
   );

   // DATA1 returns to IDLE on an accepted EOF beat.
   check_data1_to_idle_on_eof_handshake: assert property (
      @(posedge clk) disable iff (reset || clear)
      ((state == DMX_DATA1) && src_rdy_i && dst1_rdy_i && eof) |=> (state == DMX_IDLE)
   );

   // DATA1 holds until an accepted EOF beat occurs.
   check_data1_hold_without_eof_handshake: assert property (
      @(posedge clk) disable iff (reset || clear)
      ((state == DMX_DATA1) && !(src_rdy_i && dst1_rdy_i && eof)) |=> (state == DMX_DATA1)
   );

   // Any unrecognized state is corrected to IDLE on the next cycle.
   check_illegal_state_recovers_to_idle: assert property (
      @(posedge clk) disable iff (reset || clear)
      ((state != DMX_IDLE) && (state != DMX_DATA0) && (state != DMX_DATA1)) |=> (state == DMX_IDLE)
   );

endmodule