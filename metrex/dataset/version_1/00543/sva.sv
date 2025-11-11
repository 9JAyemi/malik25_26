// SVA for sram_ctrl
// Bind this module to the DUT:  bind sram_ctrl sram_ctrl_sva sva();

module sram_ctrl_sva;

  // Mirror state encodings
  localparam int ST_IDLE    = 0;
  localparam int ST_WRITE_0 = 1;
  localparam int ST_WRITE_1 = 2;
  localparam int ST_READ_0  = 3;
  localparam int ST_READ_1  = 4;
  localparam int ST_READ_2  = 5;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Reset defaults (checked during reset)
  assert property (@(posedge clk) !rst_n |-> (state==ST_IDLE &&
                                              sram_ce_n==1'b0 && sram_we_n==1'b0 && sram_oe_n==1'b1 &&
                                              sram_addr==20'd0 && sram_wr_data==16'd0 && rd_data==32'd0));

  // Legal FSM and update from next_state
  assert property (state inside {ST_IDLE,ST_WRITE_0,ST_WRITE_1,ST_READ_0,ST_READ_1,ST_READ_2});
  assert property ($past(rst_n) |-> state == $past(next_state));

  // No simultaneous read and write enables
  assert property (!(sram_we_n==1'b0 && sram_oe_n==1'b0));

  // Byte enables tied low
  assert property (sram_ub_n==1'b0 && sram_lb_n==1'b0);

  // rd_data only updates in IDLE
  assert property (state!=ST_IDLE |-> $stable(rd_data));

  // Edge detectors
  assert property ((wr_en && !$past(wr_en)) |-> wr_detc);
  assert property (wr_detc |-> (wr_en && !$past(wr_en)));
  assert property (wr_detc |=> !wr_detc);

  assert property ((clk_proc && !$past(clk_proc)) |-> clk_proc_pulse);
  assert property (clk_proc_pulse |-> (clk_proc && !$past(clk_proc)));
  assert property (clk_proc_pulse |=> !clk_proc_pulse);

  // IDLE quiet defaults
  assert property (state==ST_IDLE && !wr_detc && !(rd_en && clk_proc_pulse)
                   |-> sram_ce_n && sram_we_n && sram_oe_n && sram_addr==20'd0 && sram_wr_data==16'd0);

  // Priority: write over read when both request in IDLE
  assert property (state==ST_IDLE && wr_detc && rd_en && clk_proc_pulse
                   |-> sram_we_n==1'b0 && sram_oe_n==1'b1 && next_state==ST_WRITE_0);

  // Address mapping by state
  assert property ((state==ST_WRITE_0 || state==ST_READ_0) |-> sram_addr==20'd0);
  assert property (state==ST_WRITE_1 |-> sram_addr==addr_plus2[20:1]);
  assert property ((state==ST_READ_1 || state==ST_READ_2) |-> sram_addr==addr_plus2[20:1]);

  // Write sequence and control
  sequence wr_start; state==ST_IDLE && wr_detc; endsequence
  assert property (wr_start
                   |-> (sram_ce_n==0 && sram_we_n==0 && sram_oe_n==1 && sram_addr==addr[20:1] && sram_wr_data==wr_data[15:0])
                   ##1 (state==ST_WRITE_0 && sram_ce_n && sram_we_n && sram_oe_n && sram_addr==0 && sram_wr_data==0)
                   ##1 (state==ST_WRITE_1 && sram_ce_n==0 && sram_we_n==0 && sram_oe_n==1 && sram_addr==addr_plus2[20:1] && sram_wr_data==wr_data[31:16])
                   ##1 state==ST_IDLE);

  // Read sequence, control, and data assembly to rd_data
  sequence rd_start; state==ST_IDLE && rd_en && clk_proc_pulse; endsequence
  assert property (rd_start
                   |-> (sram_ce_n==0 && sram_we_n==1 && sram_oe_n==0 && sram_addr==addr[20:1])
                   ##1 (state==ST_READ_0 && sram_ce_n && sram_we_n && sram_oe_n==0 && sram_addr==0)
                   ##1 (state==ST_READ_1 && sram_ce_n==0 && sram_we_n==1 && sram_oe_n==0 && sram_addr==addr_plus2[20:1])
                   ##1 (state==ST_READ_2 && sram_ce_n && sram_we_n && sram_oe_n==0 && sram_addr==addr_plus2[20:1])
                   ##1 (state==ST_IDLE && rd_data == { $past(sram_rd_data,1), $past(sram_rd_data,2)}));

  // Coverage
  cover property (wr_start ##3 state==ST_IDLE);
  cover property (rd_start ##4 (state==ST_IDLE && rd_data == { $past(sram_rd_data,1), $past(sram_rd_data,2)}));
  cover property (wr_start ##3 rd_start);
  cover property (rd_start ##4 wr_start);
  cover property (state==ST_WRITE_0);
  cover property (state==ST_WRITE_1);
  cover property (state==ST_READ_0);
  cover property (state==ST_READ_1);
  cover property (state==ST_READ_2);

endmodule

bind sram_ctrl sram_ctrl_sva sva();