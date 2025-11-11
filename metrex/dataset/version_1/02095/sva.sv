// Bindable SVA for shift_register
bind shift_register shift_register_sva sv();

module shift_register_sva;
  // Use bound instance signals directly: clk, reset, enable, d, q, shift_reg

  // History availability tracker to safely use $past
  logic [2:0] hist_ok;
  always @(posedge clk) hist_ok <= {hist_ok[1:0], 1'b1};

  // Reset behavior: synchronous clear dominates
  assert property (@(posedge clk) reset |-> (shift_reg == 3'b000 && q == 1'b0));

  // Hold when disabled (no state changes without enable)
  assert property (@(posedge clk)
                   (!reset && !enable && hist_ok[0]) |-> ($stable(shift_reg) && $stable(q)));

  // Shift operation when enabled
  assert property (@(posedge clk)
                   (!reset && enable && hist_ok[0]) |-> (shift_reg == { $past(shift_reg[1:0]), $past(d)}));

  // q outputs previous MSB on a shift
  assert property (@(posedge clk)
                   (!reset && enable && hist_ok[0]) |-> (q == $past(shift_reg[2])));

  // Known values when out of reset
  assert property (@(posedge clk)
                   (!reset && hist_ok[0]) |-> !$isunknown({shift_reg,q}));

  // Back-to-back enables: q equals d delayed by 2 cycles on the 3rd consecutive enable
  assert property (@(posedge clk)
                   (!reset && hist_ok[1] && enable && $past(enable) && $past(enable,2))
                   |-> (q == $past(d,2)));

  // Coverage
  cover property (@(posedge clk) reset ##1 !reset);
  cover property (@(posedge clk) disable iff (reset) enable);
  cover property (@(posedge clk) disable iff (reset) enable ##1 enable ##1 enable);
  cover property (@(posedge clk) disable iff (reset) enable ##1 !enable [*1:$] ##1 enable);
endmodule