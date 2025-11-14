Below is a concise SVA bind module that thoroughly checks axis_averager behavior while keeping focus on high-value properties: reset, FSM, write protocol, trigger edge detect, mapping, and key coverage. Bind it to your DUT instance.


// Assertions for axis_averager
module axis_averager_sva #(
  parameter int AXIS_TDATA_WIDTH = 32,
  parameter int BRAM_DATA_WIDTH  = 32,
  parameter int BRAM_ADDR_WIDTH  = 16,
  parameter int AVERAGES_WIDTH   = 32
)(
  input  logic                          aclk,
  input  logic                          aresetn,
  input  logic                          user_reset,

  // DUT ports
  input  logic                          trig,
  input  logic [15:0]                   nsamples,
  input  logic [AVERAGES_WIDTH-1:0]     naverages,
  input  logic                          s_axis_tready,
  input  logic [AXIS_TDATA_WIDTH-1:0]   s_axis_tdata,
  input  logic                          s_axis_tvalid,
  input  logic                          bram_porta_clk,
  input  logic                          bram_porta_rst,
  input  logic [BRAM_ADDR_WIDTH-1:0]    bram_porta_addr,
  input  logic [BRAM_DATA_WIDTH-1:0]    bram_porta_wrdata,
  input  logic                          bram_porta_we,
  input  logic                          bram_portb_clk,
  input  logic                          bram_portb_rst,
  input  logic [BRAM_ADDR_WIDTH-1:0]    bram_portb_addr,
  input  logic [BRAM_DATA_WIDTH-1:0]    bram_portb_wrdata,
  input  logic [BRAM_DATA_WIDTH-1:0]    bram_portb_rddata,
  input  logic                          bram_portb_we,
  input  logic                          finished,
  input  logic [AVERAGES_WIDTH-1:0]     averages_out,

  // DUT internals (bind to these)
  input  logic [BRAM_ADDR_WIDTH-1:0]    int_addrA_reg,
  input  logic [BRAM_ADDR_WIDTH-1:0]    int_addrB_reg,
  input  logic [2:0]                    int_case_reg,
  input  logic                          int_wren_reg,
  input  logic [AVERAGES_WIDTH-1:0]     int_averages_reg,
  input  logic                          int_finished_reg,
  input  logic [BRAM_DATA_WIDTH-1:0]    int_data_reg,
  input  logic                          d_trig,
  input  logic                          trigger
);

  default clocking cb @(posedge aclk); endclocking
  function logic in_reset(); return (!aresetn || user_reset); endfunction

  // Port-to-internal mapping checks
  ap_map_ready:     assert property (s_axis_tready == 1'b1);
  ap_map_clks:      assert property (bram_porta_clk == aclk && bram_portb_clk == aclk);
  ap_map_rsts:      assert property (bram_porta_rst == ~aresetn && bram_portb_rst == ~aresetn);
  ap_map_portsA:    assert property (bram_porta_addr == int_addrA_reg && bram_porta_wrdata == int_data_reg && bram_porta_we == int_wren_reg);
  ap_map_portsB:    assert property (bram_portb_addr == int_addrB_reg && bram_portb_we == 1'b0 && bram_portb_wrdata == '0);
  ap_map_status:    assert property (finished == int_finished_reg && averages_out == int_averages_reg);

  // Reset behavior
  ap_reset_regs:    assert property (@cb in_reset() |-> (int_addrA_reg=='0 && int_addrB_reg=='0 && int_case_reg==3'd0
                                                       && int_averages_reg=='0 && int_wren_reg==0
                                                       && int_data_reg=='0 && int_finished_reg==0));
  ap_userreset_dtrig: assert property (@cb user_reset |-> (d_trig==1'b0));

  // Trigger edge detect correctness
  ap_trigger_def:   assert property (@cb trigger == (trig && !d_trig));
  ap_trigger_mask:  assert property (@cb user_reset |-> !trigger);

  // FSM legality
  ap_state_legal:   assert property (@cb int_case_reg inside {[3'd0:3'd4]});

  // 0 -> 1 transition (once out of reset)
  ap_s0_to_s1:      assert property (@cb disable iff (in_reset()) (int_case_reg==3'd0) |=> (int_case_reg==3'd1));

  // State 1: zeroing writes
  ap_s1_wren_data:  assert property (@cb disable iff (in_reset()) (int_case_reg==3'd1) |-> (int_wren_reg==1 && int_data_reg=='0));
  ap_s1_done_to_s2: assert property (@cb disable iff (in_reset())
                                     (int_case_reg==3'd1 && int_addrA_reg == nsamples-1)
                                     |=> (int_case_reg==3'd2 && int_wren_reg==0));

  // State 2: idle awaiting trigger; no writes; averages behavior
  ap_s2_nowrite:    assert property (@cb disable iff (in_reset()) (int_case_reg==3'd2) |-> (int_wren_reg==0));
  ap_s2_avg_inc:    assert property (@cb disable iff (in_reset()) (int_case_reg==3'd2 && trigger) |=> (int_averages_reg == $past(int_averages_reg)+1));
  ap_s2_avg_hold:   assert property (@cb disable iff (in_reset()) (int_case_reg==3'd2 && !trigger) |=> (int_averages_reg == $past(int_averages_reg)));

  // State 3: accumulation; handshake-driven writes
  ap_s3_write_when_valid:
                    assert property (@cb disable iff (in_reset())
                                      (int_case_reg==3'd3 && s_axis_tvalid)
                                      |=> (int_wren_reg==1
                                           && int_addrA_reg == $past(int_addrA_reg)+1
                                           && int_addrB_reg == $past(int_addrB_reg)+1
                                           && int_data_reg == ($past(bram_portb_rddata) + $past(s_axis_tdata))));
  ap_s3_nowrite_when_notvalid:
                    assert property (@cb disable iff (in_reset())
                                      (int_case_reg==3'd3 && !s_axis_tvalid)
                                      |=> (int_wren_reg==0
                                           && int_addrA_reg == $past(int_addrA_reg)
                                           && int_addrB_reg == $past(int_addrB_reg)));
  ap_s3_last_to_s2: assert property (@cb disable iff (in_reset())
                                      (int_case_reg==3'd3 && s_axis_tvalid && int_addrA_reg == nsamples-2)
                                      |=> (int_case_reg==3'd2));

  // State 4: finished is sticky; no writes
  ap_s4_finished:   assert property (@cb disable iff (in_reset()) (int_case_reg==3'd4) |-> (int_finished_reg==1 && int_wren_reg==0));
  ap_finished_sticky:
                    assert property (@cb disable iff (in_reset())
                                      $rose(finished) |-> finished[*1:$]);

  // Basic input sanity during operation (optional; tighten if desired)
  ap_nsamples_min:  assert property (@cb disable iff (in_reset())
                                     (int_case_reg inside {3'd1,3'd3,3'd2}) |-> (nsamples >= 2));

  // Coverage
  cv_zeroing:       cover property (@cb !in_reset() ##1 (int_case_reg==3'd1) ##1 (int_case_reg==3'd1 && int_addrA_reg>0));
  cv_accumulate:    cover property (@cb (int_case_reg==3'd3 && s_axis_tvalid && int_wren_reg));
  cv_finish:        cover property (@cb (int_case_reg==3'd4 && finished));

endmodule

// Example bind (instantiate once per DUT instance)
// Replace uut with your instance name.
// bind axis_averager axis_averager_sva #(
//   .AXIS_TDATA_WIDTH(AXIS_TDATA_WIDTH),
//   .BRAM_DATA_WIDTH(BRAM_DATA_WIDTH),
//   .BRAM_ADDR_WIDTH(BRAM_ADDR_WIDTH),
//   .AVERAGES_WIDTH(AVERAGES_WIDTH)
// ) sva (
//   .aclk(aclk), .aresetn(aresetn), .user_reset(user_reset),
//   .trig(trig), .nsamples(nsamples), .naverages(naverages),
//   .s_axis_tready(s_axis_tready), .s_axis_tdata(s_axis_tdata), .s_axis_tvalid(s_axis_tvalid),
//   .bram_porta_clk(bram_porta_clk), .bram_porta_rst(bram_porta_rst),
//   .bram_porta_addr(bram_porta_addr), .bram_porta_wrdata(bram_porta_wrdata), .bram_porta_we(bram_porta_we),
//   .bram_portb_clk(bram_portb_clk), .bram_portb_rst(bram_portb_rst),
//   .bram_portb_addr(bram_portb_addr), .bram_portb_wrdata(bram_portb_wrdata), .bram_portb_rddata(bram_portb_rddata), .bram_portb_we(bram_portb_we),
//   .finished(finished), .averages_out(averages_out),
//   .int_addrA_reg(int_addrA_reg), .int_addrB_reg(int_addrB_reg), .int_case_reg(int_case_reg),
//   .int_wren_reg(int_wren_reg), .int_averages_reg(int_averages_reg), .int_finished_reg(int_finished_reg),
//   .int_data_reg(int_data_reg), .d_trig(d_trig), .trigger(trigger)
// );