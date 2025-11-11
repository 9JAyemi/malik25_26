// SVA for shift_reg_mux
module shift_reg_mux_sva;
  // Bind into DUT scope to see internals
  default clocking cb @(posedge clk); endclocking

  // Static width checks (catches mux_out width bug)
  initial begin
    if ($bits(q) != 4)       $error("q must be 4 bits");
    if ($bits(shift_reg) != 4) $error("shift_reg must be 4 bits");
    if ($bits(mux_out) != 4) $error("mux_out must be 4 bits");
  end

  let mux_sel = (sel_b1 & sel_b2);

  // Async reset: immediate clear and held at 0 while asserted
  assert property (@(posedge areset) (shift_reg == 4'b0 && q == 4'b0));
  assert property (@(posedge clk) areset |-> (shift_reg == 4'b0 && q == 4'b0));

  // Shift register controls and precedence
  assert property (disable iff (areset) load |=> shift_reg == data);
  assert property (disable iff (areset) (!load && ena) |=> shift_reg == { $past(shift_reg)[2:0], $past(data[0]) });
  assert property (disable iff (areset) (!load && !ena) |=> shift_reg == $past(shift_reg));

  // Mux/output behavior (q samples pre-update shift_reg)
  assert property (disable iff (areset) mux_sel |=> q == 4'hF);
  assert property (disable iff (areset) !mux_sel |=> q == $past(shift_reg));

  // No-X on key state when not in reset
  assert property (disable iff (areset) !$isunknown(shift_reg));
  assert property (disable iff (areset) !$isunknown(q));

  // Coverage
  cover property (@(posedge areset) 1);
  cover property (disable iff (areset) load);
  cover property (disable iff (areset) (!load && ena));
  cover property (disable iff (areset) (!load && !ena));
  cover property (disable iff (areset) mux_sel);
  cover property (disable iff (areset) !mux_sel);
endmodule

bind shift_reg_mux shift_reg_mux_sva sva_inst();