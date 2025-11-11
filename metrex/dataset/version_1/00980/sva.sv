// SVA for gray_shift_register
// Bind into the DUT to access internals
bind gray_shift_register gray_shift_register_sva svai();

module gray_shift_register_sva;

  // Access DUT scope directly via bind-without-ports
  // default clocking and reset
  default clocking cb @(posedge CLK); endclocking
  default disable iff (RST);

  // Basic sanity: no X/Z after reset on key regs/outs
  assert property (!$isunknown({gray_counter_out, shift_reg,
                                counter_out, shift_reg_out, final_output})));

  // Reset behavior: next cycle after a reset cycle, regs are 0
  assert property (RST |=> (gray_counter_out==8'h00 && shift_reg==8'h00));

  // Binary counter increments by 1 every cycle (mod 256) when not crossing reset
  assert property (!$past(RST) |-> gray_counter_out == $past(gray_counter_out)+8'd1);

  // Shift register update rules (load has priority over shift)
  assert property ($past(load) |-> shift_reg == $past(data_in));
  assert property ($past(shift) && !$past(load)
                   |-> shift_reg == { $past(shift_reg[6:0]), 1'b0 });
  assert property (!$past(load) && !$past(shift)
                   |-> shift_reg == $past(shift_reg));

  // Combinational mappings
  assert property (counter_out   == (gray_counter_out ^ (gray_counter_out >> 1)));
  assert property (shift_reg_out == (shift_reg        ^ (shift_reg        >> 1)));

  // Final output mux
  assert property (select  |-> final_output == shift_reg_out);
  assert property (!select |-> final_output == counter_out);

  // Gray-code adjacency for the counter output (exactly one bit changes)
  assert property (!$past(RST) |-> $onehot(counter_out ^ $past(counter_out)));

  // ----------------
  // Useful coverage
  // ----------------
  // Counter wrap-around
  cover  property (!$past(RST) && $past(gray_counter_out)==8'hFF && gray_counter_out==8'h00);

  // Exercise load, shift, both-high precedence, and hold
  cover  property ($past(load) && shift_reg == $past(data_in));
  cover  property ($past(shift) && !$past(load)
                   && shift_reg == { $past(shift_reg[6:0]), 1'b0 });
  cover  property ($past(load && shift) && shift_reg == $past(data_in));
  cover  property (!$past(load) && !$past(shift) && shift_reg == $past(shift_reg));

  // Both mux selections observed
  cover  property (select  && final_output == shift_reg_out);
  cover  property (!select && final_output == counter_out);

endmodule