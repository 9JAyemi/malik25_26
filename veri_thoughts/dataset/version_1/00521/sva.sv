// SVA for And_Module
module And_Module_sva (
  input logic        clk,
  input logic [7:0]  a,
  input logic [7:0]  b,
  input logic [7:0]  out,
  input logic        out_valid
);
  default clocking cb @(posedge clk); endclocking

  // Functional correctness (account for NBA timing)
  property p_out_matches_and;
    1'b1 |=> (out == $past(a & b));
  endproperty
  assert property (p_out_matches_and);

  // out_valid asserts from cycle 1 and stays high
  assert property (1'b1 |=> out_valid);
  assert property (out_valid |=> out_valid);

  // No X/Z on outputs after first cycle
  assert property (1'b1 |=> (!$isunknown(out) && !$isunknown(out_valid)));

  // Tie valid to data correctness
  assert property (out_valid |-> (out == $past(a & b)));

  // Coverage
  cover property (1'b1 |=> out_valid);
  cover property ($changed(out));
  cover property ((a & b) == 8'h00);
  cover property ((a & b) == 8'hFF);
  cover property (((a & b) != 8'h00) && ((a & b) != 8'hFF));
endmodule

bind And_Module And_Module_sva sva_and (.*);