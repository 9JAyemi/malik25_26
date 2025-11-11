// SVA checkers for conflict_ff_clk and MULT9X9
// Quality-focused, concise, with key assertions and minimal but meaningful coverage.

//////////////////////////////////////////////
// conflict_ff_clk assertions
//////////////////////////////////////////////
module conflict_ff_clk_sva (
  input logic       CLK1,
  input logic       CLK2,
  input logic [8:0] B,
  input logic [17:0] Z
);
  default clocking cb2 @(posedge CLK2); endclocking

  // Z must equal {past(B), past(Z[17:9])} one CLK2 cycle later (checks both halves together)
  assert property (
    !$isunknown({$past(B), $past(Z[17:9])}) |-> Z == {$past(B), $past(Z[17:9])}
  ) else $error("conflict_ff_clk: Z update mismatch");

  // No X on B at CLK2 edge
  assert property ( !$isunknown(B) ) else $error("conflict_ff_clk: B has X at CLK2 edge");

  // Z must not change on CLK1 rising edge (guards against unintended CLK1 sensitivity and coincident edges)
  assert property (@(posedge CLK1) ##0 $stable(Z))
    else $error("conflict_ff_clk: Z changed on CLK1 edge");

  // Z must not change on CLK2 falling edge (no unintended negedge sensitivity)
  assert property (@(negedge CLK2) $stable(Z))
    else $error("conflict_ff_clk: Z changed on CLK2 negedge");

  // Coverage: demonstrate a value in B propagates to Z[8:0] two cycles later
  cover property ( $changed(B) ##2 (Z[8:0] == $past(B,1)) );
endmodule

bind conflict_ff_clk conflict_ff_clk_sva u_conflict_ff_clk_sva (
  .CLK1(CLK1), .CLK2(CLK2), .B(B), .Z(Z)
);


//////////////////////////////////////////////
// MULT9X9 assertions
//////////////////////////////////////////////
module MULT9X9_sva (
  input logic [8:0]  A,
  input logic [8:0]  B,
  input logic [17:0] Z
);
  // Combinational functional equivalence and X checking
  always @* begin
    assert (!$isunknown({A,B,Z})) else $error("MULT9X9: X detected on A/B/Z");
    assert (Z == A * B)          else $error("MULT9X9: Z != A*B");
  end

  // Simple functional coverage: non-trivial multiply exercised
  always @* begin
    cover (A!=0 && B!=0 && Z!=0);
  end
endmodule

bind MULT9X9 MULT9X9_sva u_MULT9X9_sva (
  .A(A), .B(B), .Z(Z)
);