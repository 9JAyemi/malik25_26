// SVA for bitwise_operations
module bitwise_operations_sva(
  input  [2:0] a,
  input  [2:0] b,
  input  [2:0] out_and_bitwise,
  input  [2:0] out_xor_bitwise,
  input  [2:0] out_nor_bitwise,
  input  [5:0] out_not
);

  // Evaluate on any input change; check after combinational settle
  // Functional correctness
  assert property (@(a or b) 1 |-> ##0 (out_and_bitwise == (a & b)));
  assert property (@(a or b) 1 |-> ##0 (out_xor_bitwise == (a ^ b)));
  assert property (@(a or b) 1 |-> ##0 (out_nor_bitwise == ~(a | b)));
  assert property (@(a or b) 1 |-> ##0 (out_not[5:3] == ~b && out_not[2:0] == ~a));

  // Cross-consistency: NOR equals AND of individual NOT slices
  assert property (@(a or b) 1 |-> ##0 (out_nor_bitwise == (out_not[2:0] & out_not[5:3])));

  // Outputs are known when inputs are known
  assert property (@(a or b) (!$isunknown({a,b})) |-> ##0
                   (!$isunknown({out_and_bitwise,out_xor_bitwise,out_nor_bitwise,out_not})));

  // Coverage: key corners
  cover property (@(a or b) (a==3'b000 && b==3'b000) ##0 (out_nor_bitwise==3'b111 && out_and_bitwise==3'b000));
  cover property (@(a or b) (a==3'b111 && b==3'b111) ##0 (out_and_bitwise==3'b111 && out_nor_bitwise==3'b000));
  cover property (@(a or b) (a==b)                  ##0 (out_xor_bitwise==3'b000));
  cover property (@(a or b) (a==~b)                 ##0 (out_xor_bitwise==3'b111));

endmodule

bind bitwise_operations bitwise_operations_sva sva_i(
  .a(a), .b(b),
  .out_and_bitwise(out_and_bitwise),
  .out_xor_bitwise(out_xor_bitwise),
  .out_nor_bitwise(out_nor_bitwise),
  .out_not(out_not)
);