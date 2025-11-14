// SVA for i2c_test01
module i2c_test01_sva;
  default clocking cb @(posedge clk); endclocking

  // helper for $past
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // sync reset clears on next clk
  assert property (rst |=> (cmd_stop==1'b0 && al==1'b0));

  // async nReset low clears by next clk
  assert property (!nReset |=> (cmd_stop==1'b0 && al==1'b0));

  // functional relation: after reset released, al reflects complement of previous cmd_stop
  assert property (past_valid && nReset && !rst |=> al == ~$past(cmd_stop));

  // after reset released, al stays high (given cmd_stop remains 0)
  assert property (past_valid && nReset && !rst |-> al==1'b1);

  // coverage: async reset followed by al high
  cover property ($fell(nReset) ##1 nReset ##1 (nReset && !rst && al));

  // coverage: sync reset followed by al high
  cover property ($rose(rst) ##1 (nReset && !rst && al));
endmodule

bind i2c_test01 i2c_test01_sva i2c_test01_sva_i();


// SVA for i2c_test02
module i2c_test02_sva;
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // clk_en equivalence (based on previous cnt/slave_wait due to NBA ordering)
  assert property (past_valid |-> clk_en == (($past(cnt)==16'h0000) && !$past(slave_wait)));

  // cnt next-state: decrement when non-zero
  assert property (past_valid && $past(cnt)!=16'h0000 |=> cnt == $past(cnt) - 16'h0001);

  // cnt holds at 0 when slave_wait=1
  assert property (past_valid && ($past(cnt)==16'h0000) && $past(slave_wait) |=> cnt == 16'h0000);

  // cnt reloads from clk_cnt when 0 and not waiting
  assert property (past_valid && ($past(cnt)==16'h0000) && !$past(slave_wait) |=> cnt == $past(clk_cnt));

  // cmd_stop updates only when clk_en, else holds
  assert property (past_valid && $past(clk_en) |=> cmd_stop == $past(cmd));
  assert property (past_valid && !$past(clk_en) |=> cmd_stop == $past(cmd_stop));

  // no X on key regs after first cycle
  assert property (past_valid |-> !$isunknown({clk_en, cnt, cmd_stop}));

  // coverage: reload to 1 then count down to 0
  cover property ((cnt==16'h0000 && !slave_wait && clk_cnt==1'b1) ##1 (cnt==16'h0001) ##1 (cnt==16'h0000));

  // coverage: hold at zero while waiting
  cover property ((cnt==16'h0000 && slave_wait)[*3]);

  // coverage: repeated enable pulses when clk_cnt==0
  cover property (((cnt==16'h0000) && !slave_wait && clk_cnt==1'b0)[*3]);

  // coverage: cmd_stop captures 1 then 0 on successive enables
  cover property ((clk_en && cmd) ##1 (clk_en && !cmd));
endmodule

bind i2c_test02 i2c_test02_sva i2c_test02_sva_i();