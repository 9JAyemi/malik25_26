// SVA for top_module
module top_module_sva
(
  input  logic [2:0] a,
  input  logic [2:0] b,
  input  logic [2:0] out_or_bitwise,
  input  logic       out_or_logical,
  input  logic [5:0] out_not
);

  // Sample on any input change; check after design settles (##0)
  default clocking cb @(a or b); endclocking

  // No-X on outputs when inputs are known
  assert property ( !$isunknown({a,b}) |-> ##0 !$isunknown({out_or_bitwise,out_or_logical,out_not}) );

  // Functional correctness
  assert property ( !$isunknown({a,b}) |-> ##0 (out_or_bitwise == (a | b)) );
  assert property ( !$isunknown({a,b}) |-> ##0 (out_or_logical == (|{a,b})) );
  assert property ( !$isunknown({a,b}) |-> ##0 (out_not       == ~{a,b}) );

  // Cross-consistency
  assert property ( !$isunknown({a,b}) |-> ##0 (out_or_logical == (|out_or_bitwise)) );

  // Minimal, meaningful coverage
  // Extremes
  cover property ( ##0 ! $isunknown({a,b}) && a==3'b000 && b==3'b000
                   && out_or_logical==1'b0 && out_or_bitwise==3'b000 && out_not==~6'b000000 );
  cover property ( ##0 ! $isunknown({a,b}) && a==3'b111 && b==3'b111
                   && out_or_logical==1'b1 && out_or_bitwise==3'b111 && out_not==~6'b111111 );

  // Each single-bit position across {a,b}
  cover property ( ##0 ! $isunknown({a,b}) && {a,b}==6'b000001 );
  cover property ( ##0 ! $isunknown({a,b}) && {a,b}==6'b000010 );
  cover property ( ##0 ! $isunknown({a,b}) && {a,b}==6'b000100 );
  cover property ( ##0 ! $isunknown({a,b}) && {a,b}==6'b001000 );
  cover property ( ##0 ! $isunknown({a,b}) && {a,b}==6'b010000 );
  cover property ( ##0 ! $isunknown({a,b}) && {a,b}==6'b100000 );

  // out_or_logical observed at both 0 and 1
  cover property ( ##0 ! $isunknown({a,b}) && out_or_logical==1'b0 );
  cover property ( ##0 ! $isunknown({a,b}) && out_or_logical==1'b1 );

  // Each OR bit seen asserted at least once
  cover property ( ##0 ! $isunknown({a,b}) && out_or_bitwise[0] );
  cover property ( ##0 ! $isunknown({a,b}) && out_or_bitwise[1] );
  cover property ( ##0 ! $isunknown({a,b}) && out_or_bitwise[2] );

endmodule

bind top_module top_module_sva top_module_sva_i (.*);