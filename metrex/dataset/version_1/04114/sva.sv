// SVA for ppfifo_data_generator
// Bind this checker to the DUT
bind ppfifo_data_generator ppfifo_data_generator_sva (.*);

module ppfifo_data_generator_sva (
  input               clk,
  input               rst,
  input               i_enable,
  input       [1:0]   i_wr_rdy,
  input       [23:0]  i_wr_size,
  input       [1:0]   o_wr_act,
  input               o_wr_stb,
  input       [31:0]  o_wr_data,
  input       [23:0]  r_count
);

  // Explicit reset effect check (not disabled during rst)
  assert property (@(posedge clk) rst |=> (o_wr_act==2'b00 && !o_wr_stb && o_wr_data==32'h0 && r_count==24'h0));

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Basic structural checks
  assert property ($onehot0(o_wr_act));                               // 00,01,10 only
  assert property ((o_wr_act!=2'b00 && !i_enable) |-> !o_wr_stb);     // No strobe when disabled
  assert property ((o_wr_act==2'b00) |-> !o_wr_stb);                  // No strobe when idle

  // Start behavior (entering active)
  assert property ($rose(|o_wr_act) |-> $past(i_enable) && ($past(i_wr_rdy)!=2'b00));
  assert property ($rose(|o_wr_act) |-> o_wr_act == ($past(i_wr_rdy[0]) ? 2'b01 : 2'b10));  // ch0 priority if both ready
  assert property ($rose(|o_wr_act) |=> r_count==24'd0);                                     // counter reset at start

  // Active behavior and strobe/data/count relationship
  // Exact strobe condition
  assert property (o_wr_stb == (i_enable && (o_wr_act!=2'b00) && (r_count<i_wr_size)));

  // Count increments only on strobe; data matches previous count; upper bits zero
  assert property (o_wr_stb |=> r_count == $past(r_count)+1);
  assert property (o_wr_stb |-> (o_wr_data[23:0] == $past(r_count) && o_wr_data[31:24]==8'h00));

  // When active but disabled, hold state (no strobe, no count change, act stable)
  assert property ((o_wr_act!=2'b00 && !i_enable) |-> !o_wr_stb && r_count==$past(r_count) && o_wr_act==$past(o_wr_act));

  // Completion/drop behavior
  assert property ($fell(|o_wr_act) |-> $past(i_enable) && ($past(r_count)==$past(i_wr_size)));
  assert property ((o_wr_act!=2'b00) |=> (o_wr_act==$past(o_wr_act)) || (o_wr_act==2'b00));  // no channel change mid-burst

  // Environment assumption and bound
  assume property ((o_wr_act!=2'b00) |-> $stable(i_wr_size));         // size stable while active
  assert property ((o_wr_act!=2'b00) |-> (r_count<=i_wr_size));       // counter never exceeds size

  // Coverage
  cover property ($rose(|o_wr_act) && o_wr_act==2'b01 ##[1:$] o_wr_stb [*1:$] ##1 $fell(|o_wr_act)); // ch0 burst
  cover property ($rose(|o_wr_act) && o_wr_act==2'b10 ##[1:$] o_wr_stb [*1:$] ##1 $fell(|o_wr_act)); // ch1 burst
  cover property ($rose(|o_wr_act) ##1 $fell(|o_wr_act) && !$past(o_wr_stb));                        // zero-length transfer
  cover property ($rose(|o_wr_act) ##[1:$] o_wr_stb ##1 ((o_wr_act!=2'b00)&&!i_enable)
                 ##[1:8] ((o_wr_act!=2'b00)&&i_enable) ##[1:$] o_wr_stb ##[1:$] $fell(|o_wr_act));   // pause/resume

endmodule