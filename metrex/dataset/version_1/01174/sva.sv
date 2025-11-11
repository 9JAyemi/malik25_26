// SVA for verilog_mult_32bit and its internal connectivity/behavior.
// Bind this file to the DUT. Focused, concise checks and coverage.

module verilog_mult_32bit_sva #(
  parameter din0_WIDTH = 32,
  parameter din1_WIDTH = 32,
  parameter dout_WIDTH = 32
)(
  input  logic                       clk,
  input  logic                       reset,
  input  logic                       ce,
  input  logic [din0_WIDTH-1:0]      din0,
  input  logic [din1_WIDTH-1:0]      din1,
  input  logic [dout_WIDTH-1:0]      dout,

  // internal connections in verilog_mult_32bit
  input  logic                       aclk,
  input  logic                       aclken,
  input  logic                       a_tvalid,
  input  logic [din0_WIDTH-1:0]      a_tdata,
  input  logic                       b_tvalid,
  input  logic [din1_WIDTH-1:0]      b_tdata,
  input  logic                       r_tvalid,
  input  logic [dout_WIDTH-1:0]      r_tdata,
  input  logic [din0_WIDTH-1:0]      din0_buf1,
  input  logic [din1_WIDTH-1:0]      din1_buf1
);

  // Connectivity/tie-offs
  ap_clk_conn:      assert property (@(posedge clk) disable iff (reset) aclk == clk);
  ap_ce_conn:       assert property (@(posedge clk) disable iff (reset) aclken == ce);
  ap_a_conn:        assert property (@(posedge clk) disable iff (reset) a_tdata == din0_buf1);
  ap_b_conn:        assert property (@(posedge clk) disable iff (reset) b_tdata == din1_buf1);
  ap_dout_conn:     assert property (@(posedge clk) disable iff (reset) dout == r_tdata);
  ap_valid_tied_hi: assert property (@(posedge clk) disable iff (reset) (a_tvalid === 1'b1) && (b_tvalid === 1'b1));

  // Input buffering behavior
  ap_buf_cap:  assert property (@(posedge clk) disable iff (reset) ce |-> (din0_buf1 == $past(din0) && din1_buf1 == $past(din1)));
  ap_buf_hold: assert property (@(posedge clk) disable iff (reset) !ce |-> ($stable(din0_buf1) && $stable(din1_buf1)));

  // Output update/hold behavior
  ap_dout_hold_when_ce0: assert property (@(posedge clk) disable iff (reset) !ce |-> $stable(dout));
  ap_rvalid_hold_ce0:    assert property (@(posedge clk) disable iff (reset) !ce |-> $stable(r_tvalid));

  // Functional correctness (one effective-cycle latency when ce is continuous)
  ap_mul_correct: assert property (@(posedge clk) disable iff (reset)
    (ce && $past(ce)) |-> (dout == ( $past(din0) * $past(din1) )[dout_WIDTH-1:0])
  );

  // First ce after a gap does not change output (internal stage just (re)primes)
  ap_first_ce_no_change: assert property (@(posedge clk) disable iff (reset) $rose(ce) |-> (dout == $past(dout)));

  // r_tvalid behavior under continuous enable
  ap_valid_when_streaming: assert property (@(posedge clk) disable iff (reset) (ce && $past(ce)) |-> r_tvalid);

  // X-prop guards when active
  ap_no_x_on_active: assert property (@(posedge clk) disable iff (reset) (ce && $past(ce)) |-> (!$isunknown(dout) && !$isunknown(r_tvalid)));

  // Coverage
  cp_ce_toggle:    cover property (@(posedge clk) disable iff (reset) (!ce ##1 ce ##1 !ce));
  cp_stream_mul:   cover property (@(posedge clk) disable iff (reset) (ce && $past(ce) && dout == ( $past(din0) * $past(din1) )[dout_WIDTH-1:0]));
  cp_zero_mul:     cover property (@(posedge clk) disable iff (reset) (ce && $past(ce) && (($past(din0)==0) || ($past(din1)==0)) && (dout=={dout_WIDTH{1'b0}})));
  cp_one_mul:      cover property (@(posedge clk) disable iff (reset) (ce && $past(ce) &&
                                 (($past(din0)=={{(din0_WIDTH-1){1'b0}},1'b1}) || ($past(din1)=={{(din1_WIDTH-1){1'b0}},1'b1})) &&
                                 (dout == (($past(din0)==1) ? $past(din1) : $past(din0)) [dout_WIDTH-1:0])));
  cp_allones_mul1: cover property (@(posedge clk) disable iff (reset) (ce && $past(ce) &&
                                 ($past(din0)=={din0_WIDTH{1'b1}}) && ($past(din1)=={{(din1_WIDTH-1){1'b0}},1'b1})));

endmodule

// Bind into DUT
bind verilog_mult_32bit verilog_mult_32bit_sva #(
  .din0_WIDTH(din0_WIDTH),
  .din1_WIDTH(din1_WIDTH),
  .dout_WIDTH(dout_WIDTH)
) u_verilog_mult_32bit_sva (
  .clk(clk),
  .reset(reset),
  .ce(ce),
  .din0(din0),
  .din1(din1),
  .dout(dout),
  .aclk(aclk),
  .aclken(aclken),
  .a_tvalid(a_tvalid),
  .a_tdata(a_tdata),
  .b_tvalid(b_tvalid),
  .b_tdata(b_tdata),
  .r_tvalid(r_tvalid),
  .r_tdata(r_tdata),
  .din0_buf1(din0_buf1),
  .din1_buf1(din1_buf1)
);