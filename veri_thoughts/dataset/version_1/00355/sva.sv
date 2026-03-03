// SVA for m_pc_reg
module m_pc_reg_sva (
  input logic        w_clock,
  input logic        w_reset,
  input logic [7:0]  w_bus_addr_in,
  input logic [7:0]  r_bus_addr_out
);
  default clocking @(posedge w_clock); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge w_clock) past_valid <= 1'b1;

  // Next-state function: sync reset has priority, else register captures input
  assert property (disable iff (!past_valid)
    r_bus_addr_out == ($past(w_reset) ? 8'h00 : $past(w_bus_addr_in))
  );

  // Known-value checks (avoid X/Z driving logic or flop)
  assert property (disable iff (!past_valid) !$isunknown({w_reset, r_bus_addr_out}));
  assert property (disable iff (!past_valid) (!$past(w_reset) |-> !$isunknown($past(w_bus_addr_in))));

  // Coverage: exercised reset, normal transfer, and data change
  cover property (disable iff (!past_valid) $past(w_reset) && r_bus_addr_out == 8'h00);
  cover property (disable iff (!past_valid) !$past(w_reset) && r_bus_addr_out == $past(w_bus_addr_in));
  cover property (disable iff (!past_valid) !$past(w_reset) && $changed(r_bus_addr_out));
  cover property ($rose(w_reset));
  cover property ($fell(w_reset));
endmodule

// Bind into DUT
bind m_pc_reg m_pc_reg_sva m_pc_reg_sva_i (.*);