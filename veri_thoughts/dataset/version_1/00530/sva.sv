// SVA for counter. Bind this module to the DUT instance.
// bind counter counter_sva u_counter_sva(.clk(clk), .rst(rst), .en(en), .count(count));

module counter_sva (
  input  logic       clk,
  input  logic       rst,
  input  logic       en,
  input  logic [3:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on controls and output
  ap_no_x_ctrl:  assert property (!$isunknown({rst,en}));
  ap_no_x_count: assert property (!$isunknown(count));

  // Functional behavior
  ap_sync_reset: assert property (rst |=> count == 4'd0);
  ap_hold:       assert property (!rst && !en |=> count == $past(count));
  ap_inc:        assert property (!rst && en  |=> count == $past(count) + 4'd1);

  // Changes only caused by prior en or prior rst
  ap_change_cause: assert property (!rst && $changed(count) |-> ($past(en) || $past(rst)));

  // Coverage
  cp_reset: cover property (rst ##1 count == 4'd0);
  cp_hold:  cover property (!rst && !en ##1 count == $past(count));
  cp_wrap:  cover property (!rst && en && count == 4'hF ##1 !rst && count == 4'h0);
  cp_en_burst: cover property (!rst && en [*3]); // 3-cycle enabled burst

endmodule