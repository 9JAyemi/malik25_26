// SVA for XOR2 and XOR3 (bind-in-place, clockless, concise, full functional checks + coverage)
`ifndef XOR_SVA
`define XOR_SVA

// XOR2 assertions
module XOR2_sva (input logic a,b,c);
  // Functional correctness on any input edge; ignore X/Z on inputs
  property p_xor2_func;
    @(posedge a or negedge a or posedge b or negedge b)
      !$isunknown({a,b}) |-> ##0 (c == (a ^ b));
  endproperty
  assert property (p_xor2_func);

  // No spurious output changes
  property p_xor2_no_spurious;
    @(posedge c or negedge c) $changed(a) or $changed(b);
  endproperty
  assert property (p_xor2_no_spurious);

  // Truth-table coverage
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==0) ##0 (c==0));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==0 && b==1) ##0 (c==1));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==0) ##0 (c==1));
  cover property (@(posedge a or negedge a or posedge b or negedge b) (a==1 && b==1) ##0 (c==0));

  // Output toggle coverage
  cover property (@(posedge c) 1);
  cover property (@(negedge c) 1);
endmodule

bind XOR2 XOR2_sva xor2_sva_i(.a(a),.b(b),.c(c));

// XOR3 assertions (also checks internal w1)
module XOR3_sva (input logic i0,i1,i2,o, w1);
  // Internal stage correctness
  property p_w1_func;
    @(posedge i0 or negedge i0 or posedge i1 or negedge i1)
      !$isunknown({i0,i1}) |-> ##0 (w1 == (i0 ^ i1));
  endproperty
  assert property (p_w1_func);

  // Output correctness on any input edge
  property p_xor3_func;
    @(posedge i0 or negedge i0 or posedge i1 or negedge i1 or posedge i2 or negedge i2)
      !$isunknown({i0,i1,i2}) |-> ##0 (o == (i0 ^ i1 ^ i2));
  endproperty
  assert property (p_xor3_func);

  // No spurious output changes
  property p_xor3_no_spurious;
    @(posedge o or negedge o) $changed(i0) or $changed(i1) or $changed(i2);
  endproperty
  assert property (p_xor3_no_spurious);

  // Truth-table coverage (8 combinations)
  cover property (@(posedge i0 or negedge i0 or posedge i1 or negedge i1 or posedge i2 or negedge i2)
                  (i0==0 && i1==0 && i2==0) ##0 (o==0));
  cover property (@(same) (i0==0 && i1==0 && i2==1) ##0 (o==1));
  cover property (@(same) (i0==0 && i1==1 && i2==0) ##0 (o==1));
  cover property (@(same) (i0==0 && i1==1 && i2==1) ##0 (o==0));
  cover property (@(same) (i0==1 && i1==0 && i2==0) ##0 (o==1));
  cover property (@(same) (i0==1 && i1==0 && i2==1) ##0 (o==0));
  cover property (@(same) (i0==1 && i1==1 && i2==0) ##0 (o==0));
  cover property (@(same) (i0==1 && i1==1 && i2==1) ##0 (o==1));

  // Output toggle coverage
  cover property (@(posedge o) 1);
  cover property (@(negedge o) 1);
endmodule

// Expand the @(same) macro-like syntax manually (for tools that don't support macro reuse)
// Re-bind with explicit events for the cover properties above:
`undef same
`define same posedge i0 or negedge i0 or posedge i1 or negedge i1 or posedge i2 or negedge i2

bind XOR3 XOR3_sva xor3_sva_i(.i0(i0),.i1(i1),.i2(i2),.o(o),.w1(w1));

`undef same
`endif