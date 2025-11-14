// SVA for ppfifo_data_generator
// Bind this file to the DUT

module ppfifo_data_generator_sva (
  input               clk,
  input               rst,
  input               i_enable,
  input       [1:0]   i_wr_rdy,
  input       [23:0]  i_wr_size,
  input       [1:0]   o_wr_act,
  input               o_wr_stb,
  input       [31:0]  o_wr_data
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst)

  // Structural/handshake checks
  // onehot0 on active channel
  assert property ($onehot0(o_wr_act));

  // No strobe when idle; strobe implies active
  assert property (o_wr_act==2'b00 |-> !o_wr_stb);
  assert property (o_wr_stb |-> (o_wr_act!=2'b00));

  // While active and enabled, make progress (strobe or release next cycle)
  assert property ((o_wr_act!=2'b00 && i_enable) |=> (o_wr_stb || o_wr_act==2'b00));

  // i_wr_size must stay stable during an active burst
  assert property ((o_wr_act!=2'b00 && $past(o_wr_act)!=2'b00) |-> $stable(i_wr_size));

  // Active channel cannot switch to the other channel; only drop to idle
  assert property ($changed(o_wr_act) && $past(o_wr_act)!=2'b00 |-> o_wr_act==2'b00);

  // Do not raise strobe when disabled
  assert property ((o_wr_act!=2'b00 && !i_enable) |-> !o_wr_stb);

  // Activation rules
  // If idle + enabled + any ready, must activate next cycle and choose priority 0 over 1
  assert property ((o_wr_act==2'b00 && i_enable && (i_wr_rdy!=2'b00))
                   |=> o_wr_act == ($past(i_wr_rdy[0]) ? 2'b01 : 2'b10));
  // Rising of act[0] requires ch0 ready; act[1] requires ch1 ready with ch0 not ready
  assert property ($rose(o_wr_act[0]) |-> ($past(i_enable) && $past(i_wr_rdy[0])));
  assert property ($rose(o_wr_act[1]) |-> ($past(i_enable) && !$past(i_wr_rdy[0]) && $past(i_wr_rdy[1])));

  // Data/strobe semantics
  // Upper bits must be zero; data must be strictly less than size on each strobe
  assert property (o_wr_stb |-> (o_wr_data[31:24]==8'h00));
  assert property (o_wr_stb |-> (o_wr_data < i_wr_size));

  // On consecutive strobe cycles, data increments by 1
  assert property ((o_wr_stb && $past(o_wr_stb)) |-> (o_wr_data == $past(o_wr_data)+1));

  // Last strobe (data==size-1) must be followed by release
  assert property ((o_wr_stb && (o_wr_data == i_wr_size-1)) |=> (o_wr_act==2'b00));

  // Zero-size burst: immediate release, no strobe
  assert property (($rose(o_wr_act!=2'b00) && $past(i_wr_size)==0) |=> (!o_wr_stb && o_wr_act==2'b00));

  // Reset drives outputs low
  assert property (disable iff (1'b0) @(posedge clk) rst |-> (o_wr_act==2'b00 && o_wr_stb==1'b0 && o_wr_data==32'h0));

  // Functional coverage
  // Priority selection to ch0 when both ready
  cover property (o_wr_act==2'b00 && i_enable && i_wr_rdy==2'b11 ##1 o_wr_act==2'b01
                  ##[1:$] (o_wr_stb && o_wr_data==i_wr_size-1) ##1 o_wr_act==2'b00);

  // Activate ch1 when only ch1 ready
  cover property (o_wr_act==2'b00 && i_enable && i_wr_rdy==2'b10 ##1 o_wr_act==2'b10
                  ##[1:$] (o_wr_stb && o_wr_data==i_wr_size-1) ##1 o_wr_act==2'b00);

  // Zero-length burst
  cover property ($rose(o_wr_act!=2'b00) && $past(i_wr_size)==0 ##1 o_wr_act==2'b00);

  // Pause/resume mid-burst via i_enable deassertion
  cover property ($rose(o_wr_act!=2'b00) ##[1:$] o_wr_stb ##1 !i_enable [*1:$]
                  ##1 i_enable ##[1:$] (o_wr_stb && o_wr_data==i_wr_size-1) ##1 o_wr_act==2'b00);

endmodule

bind ppfifo_data_generator ppfifo_data_generator_sva sva_i (
  .clk(clk),
  .rst(rst),
  .i_enable(i_enable),
  .i_wr_rdy(i_wr_rdy),
  .i_wr_size(i_wr_size),
  .o_wr_act(o_wr_act),
  .o_wr_stb(o_wr_stb),
  .o_wr_data(o_wr_data)
);