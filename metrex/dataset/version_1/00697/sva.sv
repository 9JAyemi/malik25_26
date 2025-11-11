// SVA for top_module/counter_module/shift_register_module

module counter_module_sva (input clk, reset, input [3:0] q);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  a_cnt_reset_next: assert property (cb reset |=> q == 4'h0);
  a_cnt_reset_hold: assert property (cb reset && $past(reset) |-> q == 4'h0);

  // Count up modulo-16 when not in reset
  a_cnt_inc:        assert property (cb disable iff (reset) q == $past(q) + 4'd1);

  // No X after reset deasserted
  a_cnt_no_x:       assert property (cb disable iff (reset) !$isunknown(q));

  // Coverage: wrap-around
  c_cnt_wrap:       cover  property (cb $past(q)==4'hF && !reset ##1 q==4'h0);
endmodule

module shift_register_module_sva (input clk, reset, input SER_IN, SH_EN, input [3:0] q);
  default clocking cb @(posedge clk); endclocking

  // Inputs known when used
  a_sr_in_known:    assert property (cb disable iff (reset) !$isunknown({SH_EN,SER_IN}));

  // Reset behavior
  a_sr_reset_next:  assert property (cb reset |=> q == 4'h0);
  a_sr_reset_hold:  assert property (cb reset && $past(reset) |-> q == 4'h0);

  // Shift/hold behavior
  a_sr_shift:       assert property (cb disable iff (reset) SH_EN |=> q == { $past(q[2:0]), $past(SER_IN) });
  a_sr_hold:        assert property (cb disable iff (reset) !SH_EN |=> q == $past(q));

  // No X after reset deasserted
  a_sr_no_x:        assert property (cb disable iff (reset) !$isunknown(q));

  // Coverage
  c_sr_shift0:      cover  property (cb disable iff (reset) SH_EN && SER_IN==1'b0);
  c_sr_shift1:      cover  property (cb disable iff (reset) SH_EN && SER_IN==1'b1);
  c_sr_hold:        cover  property (cb disable iff (reset) !SH_EN);
endmodule

module top_module_sva (input clk, reset, input SER_IN, SH_EN,
                       input [7:0] q,
                       input [3:0] counter, shift_reg);
  default clocking cb @(posedge clk); endclocking

  // Combinational concatenation must match
  a_top_concat:     assert property (cb q == {counter, shift_reg});

  // If parts are known, output must be known
  a_top_no_x:       assert property (cb disable iff (reset)
                             !$isunknown({counter,shift_reg}) |-> !$isunknown(q));

  // Coverage: observe at least one concatenation change
  c_top_change:     cover  property (cb !$stable({counter,shift_reg}));
endmodule

// Bind assertions
bind counter_module         counter_module_sva         cm_sva   (.clk(clk), .reset(reset), .q(q));
bind shift_register_module  shift_register_module_sva  sr_sva   (.clk(clk), .reset(reset), .SER_IN(SER_IN), .SH_EN(SH_EN), .q(q));
bind top_module             top_module_sva             top_sva  (.clk(clk), .reset(reset), .SER_IN(SER_IN), .SH_EN(SH_EN),
                                                                 .q(q), .counter(counter), .shift_reg(shift_reg));