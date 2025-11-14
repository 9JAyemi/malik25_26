// SVA for module top. Bind this to the DUT.
// Note: 'do' is a SystemVerilog keyword; use escaped identifier \do when binding.

module top_sva (
  input  logic [3:0] di,
  input  logic       do_o,   // bound to \do
  input  logic [3:0] d
);

  default clocking cb @(di or d or do_o); endclocking

  // Inverters are correct
  genvar i;
  for (i=0; i<4; i++) begin
    assert property (##0 d[i] === ~di[i]);
    cover  property (##0 (di[i]===1'b0 && d[i]===1'b1));
    cover  property (##0 (di[i]===1'b1 && d[i]===1'b0));
  end

  // Structural equation of output
  assert property (##0 do_o === ~((d[1] & d[0]) | (d[3] & d[2])));

  // Simplified functional equivalence (De Morgan)
  let t_lo = (di[1] | di[0]);
  let t_hi = (di[3] | di[2]);
  assert property (##0 do_o === (t_lo & t_hi));

  // Basic X/Z hygiene: known inputs imply known internals/output
  assert property (##0 !$isunknown(di) |-> (!$isunknown(d) && !$isunknown(do_o)));

  // Functional implications (concise sanity)
  assert property (##0 (t_lo==1'b0) |-> do_o==1'b0);
  assert property (##0 (t_hi==1'b0) |-> do_o==1'b0);
  assert property (##0 (t_lo && t_hi) |-> do_o==1'b1);

  // Coverage: OR terms hit 0/1, both NAND legs exercised, output toggles
  cover property (##0 (t_lo==1'b0));
  cover property (##0 (t_lo==1'b1));
  cover property (##0 (t_hi==1'b0));
  cover property (##0 (t_hi==1'b1));
  cover property (##0 (d[1] & d[0]));
  cover property (##0 (d[3] & d[2]));
  cover property ($rose(do_o));
  cover property ($fell(do_o));

endmodule

bind top top_sva u_top_sva (.di(di), .do_o(\do ), .d(d));