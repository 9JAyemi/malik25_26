// SVA for top_module
// Bind this to the DUT: bind top_module top_module_sva sva();

// Concise, high-signal-coverage assertions and covers.
module top_module_sva;

  // Connectivity checks (ensure outputs match internal regs)
  assert property (@(posedge clk) counter_out   == counter);
  assert property (@(posedge clk) shift_reg_out == shift_reg);
  assert property (@(posedge clk) final_output  == sum);

  // Counter: async reset value observed at posedge; increments by 1 when not in reset
  assert property (@(posedge clk) reset |-> counter == 4'b1000);

  assert property (@(posedge clk)
                   !reset && !$past(reset) && !$isunknown($past(counter))
                   |-> counter == $past(counter) + 4'd1);

  // While in reset across cycles, counter holds reset value
  assert property (@(posedge clk)
                   reset && $past(reset) |-> counter == 4'b1000);

  // Shift register should not change on posedge clk (only updates on negedge)
  assert property (@(posedge clk) $stable(shift_reg));

  // Intended circular/serial behavior on negedge:
  // - Upper 7 bits shift left by 1
  assert property (@(negedge clk)
                   !$isunknown($past(shift_reg))
                   |-> shift_reg[7:1] == $past(shift_reg[6:0]));

  // - New LSB captures d[0] (detects width/concatenation bug in RTL)
  assert property (@(negedge clk)
                   !$isunknown(shift_reg[0]) |-> shift_reg[0] == d[0]);

  // Sum/final_output combinational correctness (check at both edges)
  assert property (@(posedge clk) sum == shift_reg + counter);
  assert property (@(posedge clk) final_output == shift_reg + counter);
  assert property (@(negedge clk) final_output == shift_reg + counter);

  // Basic “no X” on observable outputs when operands are known
  assert property (@(posedge clk)
                   !$isunknown(shift_reg) && !$isunknown(counter)
                   |-> !$isunknown(final_output));

  // Coverage
  // Counter wraps (mod-16 behavior)
  cover property (@(posedge clk) !reset ##1 counter==4'hF ##1 counter==4'h0);

  // Reset then first post-reset increment to 9
  cover property (@(posedge clk) reset ##1 !reset ##1 counter==4'd9);

  // Shift captures both 0 and 1 on serial input bit
  cover property (@(negedge clk) (d[0]==0) ##1 (d[0]==1));

  // Addition overflow (final_output wrapped below shift_reg)
  cover property (@(posedge clk) !reset && final_output < shift_reg);

endmodule