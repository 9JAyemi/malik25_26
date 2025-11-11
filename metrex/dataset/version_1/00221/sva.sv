// SVA for dyn_pll_ctrl
// Recommend using bind:
// bind dyn_pll_ctrl dyn_pll_ctrl_sva #(.SPEED_MHZ(SPEED_MHZ), .SPEED_LIMIT(SPEED_LIMIT), .SPEED_MIN(SPEED_MIN), .OSC_MHZ(OSC_MHZ)) svai (.*);

module dyn_pll_ctrl_sva #(
  parameter SPEED_MHZ  = 25,
  parameter SPEED_LIMIT= 100,
  parameter SPEED_MIN  = 25,
  parameter OSC_MHZ    = 100
)(
  input  logic         clk,
  input  logic         clk_valid,
  input  logic         locked,
  input  logic [7:0]   speed_in,
  input  logic         start,
  input  logic         progclk,
  input  logic         progdata,
  input  logic         progen,
  input  logic         reset,
  input  logic [7:0]   state,
  input  logic [23:0]  watchdog,
  input  logic [7:0]   dval,
  input  logic [7:0]   mval,
  input  logic [2:1]   status
);

  default clocking cb @(posedge clk); endclocking

  // Helper predicates
  function automatic bit in_range(byte v);
    return (v >= SPEED_MIN) && (v <= SPEED_LIMIT);
  endfunction

  sequence s_start_acc;
    clk_valid && (state==0) && progclk && (start || $past(start)) && in_range(speed_in);
  endsequence

  // 1) progclk free-run toggle
  ap_progclk_toggle: assert property (progclk == ~$past(progclk));

  // 2) Start acceptance and rejection
  ap_start_accept: assert property (
    s_start_acc |=> state==8'd1 && progen==1'b0 && progdata==1'b0 && mval==speed_in && dval==OSC_MHZ
  );

  ap_start_reject_bad: assert property (
    clk_valid && (state==0) && (start || $past(start)) && (!progclk || !in_range(speed_in))
    |=> state==8'd0
  );

  // 3) Clear on clk_valid deassert
  ap_clear_on_clk_invalid: assert property ((!clk_valid) |=> (state==8'd0 && progen==1'b0 && progdata==1'b0));

  // 4) State progression and wrap
  ap_state_inc:  assert property (clk_valid && (state inside {[8'd1:8'd253]}) |=> state == $past(state)+8'd1);
  ap_state_wrap: assert property (clk_valid && state==8'd254 |=> state==8'd0);

  // 5) First word (dval) programming protocol
  ap_d_hdr:      assert property (state==8'd2  |-> (progen==1'b1 && progdata==1'b1));
  ap_d_zero:     assert property (state==8'd4  |-> (progdata==1'b0));
  ap_d_bits:     assert property ((state inside {8'd6,8,10,12,14,16,18,20}) |-> (progen==1'b1 && progdata == $past(dval[0])));
  ap_d_shift:    assert property ((state inside {8'd6,8,10,12,14,16,18,20}) |=> (dval[6:0] == $past(dval[7:1]) && dval[7] == $past(dval[7])));
  ap_d_end:      assert property (state==8'd22 |-> (progen==1'b0 && progdata==1'b0));
  ap_d_progen_hi_window: assert property ((state inside {[8'd2:8'd21]}) |-> progen==1'b1);

  // 6) Second word (mval) programming protocol
  ap_m_hdr:      assert property (state==8'd32 |-> (progen==1'b1 && progdata==1'b1));
  ap_m_bits:     assert property ((state inside {8'd36,38,40,42,44,46,48,50}) |-> (progen==1'b1 && progdata == $past(mval[0])));
  ap_m_shift:    assert property ((state inside {8'd36,38,40,42,44,46,48,50}) |=> (mval[6:0] == $past(mval[7:1]) && mval[7] == $past(mval[7])));
  ap_m_end:      assert property (state==8'd52 |-> (progen==1'b0 && progdata==1'b0));
  ap_m_progen_hi_window: assert property ((state inside {[8'd32:8'd51]}) |-> progen==1'b1);

  // 7) Post-program pulses
  ap_pulse_62:   assert property (state==8'd62 |-> progen==1'b1);
  ap_pulse_64:   assert property (state==8'd64 |-> progen==1'b0);

  // 8) Output change legality (no unexpected transitions)
  function automatic bit acc_now();
    return (clk_valid && state==0 && progclk && (start || $past(start)) && in_range(speed_in));
  endfunction

  ap_progen_change_legal: assert property (
    $changed(progen) |-> ( (state inside {8'd2,8'd22,8'd32,8'd52,8'd62,8'd64}) || !clk_valid || acc_now() )
  );

  ap_progdata_change_legal: assert property (
    $changed(progdata) |-> ( (state inside {8'd2,8'd4,8'd6,8'd8,8'd10,8'd12,8'd14,8'd16,8'd18,8'd20,
                                            8'd22,8'd32,8'd36,8'd38,8'd40,8'd42,8'd44,8'd46,8'd48,8'd50,8'd52})
                              || !clk_valid || acc_now() )
  );

  // 9) Watchdog/reset behavior
  ap_wd_clr_on_locked: assert property (locked |-> watchdog==24'd0);
  ap_wd_inc:           assert property ((!locked && !$past(watchdog[23])) |-> watchdog == $past(watchdog)+24'd1);
  ap_wd_timeout:       assert property ($past(watchdog[23]) |-> (reset==1'b1 && watchdog==24'd0));
  ap_reset_one_cycle:  assert property (reset |=> !reset);

  // 10) Coverage
  cv_full_program: cover property (
    s_start_acc
    ##1 (state==8'd2)
    ##[1:$] (state==8'd22)
    ##[1:$] (state==8'd32)
    ##[1:$] (state==8'd52)
    ##[1:20] (state==8'd62)
    ##1 (state==8'd64)
    ##[1:$] (state==8'd0)
  );

  cv_edge_min: cover property (clk_valid && state==0 && progclk && start && (speed_in==SPEED_MIN));
  cv_edge_max: cover property (clk_valid && state==0 && progclk && start && (speed_in==SPEED_LIMIT));

  cv_reject_out_of_range: cover property (
    clk_valid && state==0 && progclk && start && !in_range(speed_in) ##1 state==0
  );

  cv_abort_on_clk_invalid: cover property (s_start_acc ##[1:40] !clk_valid);

  cv_watchdog_timeout: cover property ($past(watchdog[23]) ##1 reset);

endmodule