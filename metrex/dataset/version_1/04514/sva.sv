// SVA for counter: concise, high-quality checks + coverage
module counter_sva (input logic CLK, RST, EN, input logic [3:0] Q);
  default clocking cb @(posedge CLK); endclocking

  // Sanity/X checks
  a_no_x_ctl:  assert property (!$isunknown({RST,EN}));
  a_no_x_out:  assert property (disable iff (RST) !$isunknown(Q));

  // Reset behavior (synchronous, priority over EN)
  a_rst_clear: assert property (RST |=> Q == 4'h0);
  a_rst_hold:  assert property ((RST && $past(RST)) |-> Q == 4'h0);

  // Functional behavior (using Q as the architectural state)
  a_hold:      assert property (disable iff (RST) (!EN) |=> Q == $past(Q));
  a_inc:       assert property (disable iff (RST) ( EN) |=> Q == ($past(Q)+5'd1)[3:0]);
  a_wrap:      assert property (disable iff (RST || $past(RST)))
                               ($past(EN) && $past(Q)==4'hF) |-> Q==4'h0);

  // Coverage: reset, hold, increment, wrap
  c_reset:     cover  property (RST |=> Q==4'h0);
  c_hold:      cover  property (disable iff (RST) !EN |=> Q==$past(Q));
  c_inc:       cover  property (disable iff (RST)  EN |=> Q==($past(Q)+5'd1)[3:0]);
  c_wrap:      cover  property (disable iff (RST) (Q==4'hF && EN) |=> (Q==4'h0));
endmodule

// Bind into the DUT
bind counter counter_sva sva_counter (.CLK(CLK), .RST(RST), .EN(EN), .Q(Q));