// SVA for accu
module accu_sva;
  // Assume bind into accu scope so these names are visible
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Async reset effect at clock
  assert property (@(posedge clk) !rst_n |-> (data_reg==8'h00 && count_reg==4'h0 && valid_b==1'b0 && data_out==10'h000));

  // No X after reset deasserted
  assert property (!$isunknown({valid_b, ready_a, data_out, data_reg, count_reg}));

  // Combinational relation
  assert property (ready_a == (~valid_b & ready_b));

  // Accumulate/hold behavior
  assert property ($past(rst_n) &&  valid_a |=> (data_reg == $past(data_reg) + $past(data_in) &&
                                                 count_reg == $past(count_reg) + 4'd1));
  assert property ($past(rst_n) && !valid_a |=> (data_reg == $past(data_reg) &&
                                                 count_reg == $past(count_reg)));

  // Output/valid generation when count==15 (uses pre-update regs)
  assert property ($past(rst_n) && (count_reg==4'hF) |=> (valid_b && data_out == { $past(data_reg), 2'b00 }));
  assert property ($past(rst_n) && (count_reg!=4'hF) |=> (valid_b == $past(valid_b) && data_out == $past(data_out)));

  // valid_b protocol
  assert property ($rose(valid_b) |-> $past(count_reg)==4'hF);
  assert property (valid_b |=> valid_b); // sticky once set

  // data_out properties
  assert property (data_out[1:0] == 2'b00); // always 4-aligned
  assert property ($past(rst_n) && $changed(data_out) |-> $past(count_reg)==4'hF);

  // Coverage
  cover property ($rose(rst_n));
  cover property (ready_a);
  cover property ($rose(valid_b));
  cover property (count_reg==4'hF);
  cover property (count_reg==4'hF && valid_a);
  cover property ($rose(valid_b) && $past(data_reg)!=8'h00 && data_out=={ $past(data_reg),2'b00 });
endmodule

bind accu accu_sva acc_sva();