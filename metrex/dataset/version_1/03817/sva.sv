// SVA for shift_register
// Bind this to the DUT or instantiate alongside.

module shift_register_sva (
  input logic        clk,
  input logic        load,
  input logic        clear,
  input logic [7:0]  data_in,
  input logic [7:0]  data_out
);

  default clocking cb @(posedge clk); endclocking

  // Control signals must be known each cycle
  assert property (cb !$isunknown({clear, load}));

  // Priority/behavior checks (synchronous)
  // clear dominates and forces zero next cycle
  assert property (cb clear |=> data_out == 8'h00);

  // load (when not clearing) captures data_in next cycle
  assert property (cb (!clear && load) |=> data_out == $past(data_in));

  // rotate-left by 1 when neither clear nor load
  assert property (cb (!clear && !load)
                   |=> data_out == {$past(data_out)[6:0], $past(data_out)[7]});

  // Explicit dominance when both asserted
  assert property (cb (clear && load) |=> data_out == 8'h00);

  // Some concise functional coverages
  cover property (cb clear);
  cover property (cb (!clear && load));
  cover property (cb (!clear && !load));

  // See both asserted together (priority case)
  cover property (cb (clear && load));

  // Back-to-back loads
  cover property (cb (!clear && load) ##1 (!clear && load));

  // Load then rotate
  cover property (cb (!clear && load) ##1 (!clear && !load));

  // Sustained clear holds zero
  cover property (cb clear [*3] ##1 data_out == 8'h00);

  // 8 consecutive rotates return to original value
  cover property (cb (!clear && !load)[*8] ##1 (data_out == $past(data_out,8)));

endmodule

// Bind to the DUT
bind shift_register shift_register_sva sva_i (
  .clk(clk),
  .load(load),
  .clear(clear),
  .data_in(data_in),
  .data_out(data_out)
);