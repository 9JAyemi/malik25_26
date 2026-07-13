module alu_16bit_sva(A, B, op, Y);
  input logic [15:0] A, B;
  input logic [3:0] op;
  input logic [15:0] Y;

  // Combinational logic, so use @(posedge clk)
  // No clock or reset signals are present in the RTL

  // ALU operations
  // Addition
  add_check: assert property (
      @(posedge clk) disable iff (1'b0) (op == 4'b0000) |-> (Y == A + B)
  );
  // Subtraction
  sub_check: assert property (
      @(posedge clk) disable iff (1'b0) (op == 4'b0001) |-> (Y == A - B)
  );
  // Bitwise AND
  and_check: assert property (
      @(posedge clk) disable iff (1'b0) (op == 4'b0010) |-> (Y == A & B)
  );
  // Bitwise OR
  or_check: assert property (
      @(posedge clk) disable iff (1'b0) (op == 4'b0011) |-> (Y == A | B)
  );
  // Bitwise XOR
  xor_check: assert property (
      @(posedge clk) disable iff (1'b0) (op == 4'b0100) |-> (Y == A ^ B)
  );
  // Bitwise NOT
  not_check: assert property (
      @(posedge clk) disable iff (1'b0) (op == 4'b0101) |-> (Y == ~A)
  );
  // Shift Left
  shift_left_check: assert property (
      @(posedge clk) disable iff (1'b0) (op == 4'b0110) |-> (Y == {A[14:0], 1'b0})
  );
  // Shift Right
  shift_right_check: assert property (
      @(posedge clk) disable iff (1'b0) (op == 4'b0111) |-> (Y == {1'b0, A[15:1]})
  );
  // Rotate Left
  rotate_left_check: assert property (
      @(posedge clk) disable iff (1'b0) (op == 4'b1000) |-> (Y == {A[14:0], A[15]})
  );
  // Rotate Right
  rotate_right_check: assert property (
      @(posedge clk) disable iff (1'b0) (op == 4'b1001) |-> (Y == {A[0], A[15:1]})
  );
endmodule