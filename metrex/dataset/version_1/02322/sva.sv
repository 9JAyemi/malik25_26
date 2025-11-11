// SVA for multiplier
// Uses $global_clock for combinational sampling; bind to DUT below.

module multiplier_sva (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic [7:0] result
);
  default clocking cb @($global_clock); endclocking

  // Golden model
  let mul_model = ( $unsigned(a) * $unsigned(b) );

  // Functional correctness (primary check)
  assert property ( !$isunknown({a,b}) |-> (result == mul_model) );

  // Basic identities
  assert property ( (!$isunknown({a,b}) && ((a==0) || (b==0))) |-> (result == 8'd0) );
  assert property ( (!$isunknown({a,b}) && (a==4'd1)) |-> (result == {4'b0,b}) );
  assert property ( (!$isunknown({a,b}) && (b==4'd1)) |-> (result == {4'b0,a}) );
  assert property ( !$isunknown({a,b}) |-> (result[0] == (a[0] & b[0])) );

  // Output known when inputs known
  assert property ( !$isunknown({a,b}) |-> !$isunknown(result) );

  // Pure combinational behavior: output stable when inputs stable
  assert property ( $stable({a,b}) |-> $stable(result) );

  // Range bound (max 15*15 = 225)
  assert property ( !$isunknown({a,b}) |-> (result <= 8'd225) );

  // Coverage
  cover property ( !$isunknown({a,b}) && (result == mul_model) ); // functional hit
  covergroup cg_ab @(cb);
    coverpoint a { bins all[] = {[0:15]}; }
    coverpoint b { bins all[] = {[0:15]}; }
    cross a, b; // full 4x4 operand cross coverage
  endgroup
  cg_ab cg_inst = new();

  // Corner covers
  cover property (a==0 && b==0);
  cover property (a==0 && b!=0);
  cover property (b==0 && a!=0);
  cover property (a==4'hF && b==4'hF);
  cover property (a==b);
endmodule

bind multiplier multiplier_sva sva_i (.*);