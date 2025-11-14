// SVA for top_module
module top_module_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset behavior (checked even while reset is 1)
  assert property (@(posedge clk) disable iff (1'b0) reset |-> (acc1==0 && count1==0 && acc2==0 && sum==0 && count2==0 && select_reg==0));
  assert property (@(posedge clk) disable iff (1'b0) reset |=> (acc1==0 && count1==0 && acc2==0 && sum==0 && count2==0 && select_reg==0));

  // Basic sanity / muxing / handshake
  assert property (!$isunknown({data_out, ready_a, valid_a}));
  assert property (ready_a == valid_b);
  assert property (data_out[1:0] == 2'b00);
  assert property ((select_reg==0) |-> data_out[9:2] == acc1);
  assert property ((select_reg!=0) |-> data_out[9:2] == acc2);
  assert property (select_reg[1] == 1'b0); // width-cast of 1-bit select

  // Select pipeline
  assert property ($past(!reset) |-> select_reg == $past(select));

  // Valid generation correctness
  assert property (valid_a == ((select_reg==0) ? (count1==3'd7) : (count2==2'd1)));

  // acc1: counter/datapath
  assert property ((count1 != 3'd7) |=> (count1 == $past(count1)+3'd1 && acc1 == $past(acc1)));
  assert property ((count1 == 3'd7) |=> (count1 == 3'd0 && acc1 == $past(acc1) + $past(data_in)));

  // acc2: counter domain and datapath
  assert property (count2 inside {2'd0,2'd1});
  assert property ((count2 == 2'd0) |=> (count2 == 2'd1 && sum == $past(sum) + $past(data_in) && acc2 == $past(acc2)));
  assert property ((count2 == 2'd1) |=> (count2 == 2'd0 && sum == 8'd0 && acc2 == $past(acc2) + $past(sum)));

  // Valid implies selected accumulator updated
  assert property (valid_a |-> ((select_reg==0 && $changed(acc1)) || (select_reg!=0 && $changed(acc2))));

  // Coverage
  cover property ($rose(!reset));
  cover property ((count1==3'd7) ##1 (count1==3'd0));
  cover property ((count2==2'd0) ##1 (count2==2'd1) ##1 (count2==2'd0));
  cover property ((select_reg==0) ##1 (count1==3'd7));
  cover property ((select_reg!=0) ##1 (count2==2'd1));
  cover property ((select_reg==0) ##1 (select_reg!=0) ##1 (select_reg==0));
endmodule

bind top_module top_module_sva sva_top_module();