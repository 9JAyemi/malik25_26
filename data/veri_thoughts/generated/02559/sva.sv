module four_bit_adder_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       C,
  input logic [3:0] S
);
  // Combinational DUT with no clock/reset; sample properties on C edges.

  // S must equal (C ? (A & B) : (A ^ B)) on any C edge.
  check_select_function: assert property (
    @(posedge C or negedge C) S == (C ? (A & B) : (A ^ B))
  );

  // On rising C, S equals bitwise AND of A and B.
  check_and_on_C_high: assert property (
    @(posedge C) S == (A & B)
  );

  // On falling C, S equals bitwise XOR of A and B.
  check_xor_on_C_low: assert property (
    @(negedge C) S == (A ^ B)
  );

  // When inputs are equal and C is low, XOR result (S) is zero.
  check_xor_zero_when_equal: assert property (
    @(negedge C) (A == B) |-> (S == 4'b0000)
  );

  // When either input is zero and C is high, AND result (S) is zero.
  check_and_zero_when_any_zero: assert property (
    @(posedge C) ((A == 4'b0000) || (B == 4'b0000)) |-> (S == 4'b0000)
  );

  // When both inputs are all ones and C is high, AND result (S) is all ones.
  check_and_all_ones: assert property (
    @(posedge C) (A == 4'b1111 && B == 4'b1111) |-> (S == 4'b1111)
  );
endmodule