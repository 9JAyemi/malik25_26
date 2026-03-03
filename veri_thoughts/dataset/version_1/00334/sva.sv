// SVA for the given design. Concise, bound to DUT modules. No TB code.

// Assertions for ALU
module alu_sva (
  input logic [3:0] A, B,
  input logic [2:0] OP,
  input logic [3:0] P
);
  default clocking cb @(*); endclocking

  // Functional correctness per OP
  a_and:  assert property (OP==3'b000 |-> P == (A & B));
  a_or:   assert property (OP==3'b001 |-> P == (A | B));
  a_add:  assert property (OP==3'b010 |-> P == (A + B));
  a_sub:  assert property (OP==3'b011 |-> P == (A - B));
  a_xor:  assert property (OP==3'b100 |-> P == (A ^ B));
  a_not:  assert property (OP==3'b101 |-> P == (~A));
  a_sll1: assert property (OP==3'b110 |-> P == (A << 1));
  a_srl1: assert property (OP==3'b111 |-> P == (A >> 1));

  // No X on output for any legal OP
  a_nox:  assert property (!$isunknown(P));

  // Coverage: hit all ops
  cover property (OP==3'b000);
  cover property (OP==3'b001);
  cover property (OP==3'b010);
  cover property (OP==3'b011);
  cover property (OP==3'b100);
  cover property (OP==3'b101);
  cover property (OP==3'b110);
  cover property (OP==3'b111);
endmodule

// Assertions for comparator/priority encoder
module comp_sva (
  input logic [3:0] a, b,
  input logic [2:0] comparison_result
);
  default clocking cb @(*); endclocking

  c_gt:    assert property ((a > b) |-> comparison_result == 3'b010);
  c_lt:    assert property ((a < b) |-> comparison_result == 3'b001);
  c_eq:    assert property ((a == b) |-> comparison_result == 3'b000);

  // Only 000/001/010 are allowed encodings
  c_valid: assert property (comparison_result inside {3'b000,3'b001,3'b010});

  // No X on output
  c_nox:   assert property (!$isunknown(comparison_result));

  // Coverage: hit all 3 relations and codes
  cover property (a > b && comparison_result == 3'b010);
  cover property (a < b && comparison_result == 3'b001);
  cover property (a == b && comparison_result == 3'b000);
endmodule

// Assertions for top mapping to final_output
module top_sva (
  input logic [3:0] alu_result,
  input logic [2:0] comparison_result,
  input logic [1:0] final_output
);
  default clocking cb @(*); endclocking

  // Exact functional equivalence to RTL expression
  t_eq: assert property (
    final_output == ((comparison_result == 3'b011 && alu_result == 4'b0000) ? 2'b10 :
                     (comparison_result == 3'b010) ? 2'b01 :
                     (comparison_result == 3'b001) ? 2'b00 :
                     2'b11)
  );

  // Given comparator encoding, 2'b10 should be unreachable
  t_no10: assert property (final_output != 2'b10);

  // Sanity: no X on output
  t_nox: assert property (!$isunknown(final_output));

  // Coverage: observe all reachable final_output values
  cover property (final_output == 2'b00);
  cover property (final_output == 2'b01);
  cover property (final_output == 2'b11);
  // Optional: attempt to cover unreachable 2'b10 (expected 0 hits)
  cover property (final_output == 2'b10);
endmodule

// Bind assertions to DUT
bind alu                        alu_sva alu_sva_i (.*);
bind mag_comp_priority_encoder  comp_sva comp_sva_i (.*);
bind top_module                 top_sva  top_sva_i  (.alu_result(alu_result),
                                                     .comparison_result(comparison_result),
                                                     .final_output(final_output));