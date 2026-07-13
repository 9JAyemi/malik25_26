module binary_add_sub_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic mode,
  output logic [3:0] Y
);
  // Combinational logic, so use @(posedge clk)
  // Addition operation when mode is 0
  add_operation: assert property (
    @(posedge clk) disable iff (!reset_n) (mode == 0) |-> (Y == A + B)
  );
  // Subtraction operation when mode is 1
  sub_operation: assert property (
    @(posedge clk) disable iff (!reset_n) (mode == 1) |-> (Y == A + (~B + 1))
  );
endmodule