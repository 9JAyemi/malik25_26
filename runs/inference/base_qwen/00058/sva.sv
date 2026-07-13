module calculator_sva (
  input logic [7:0] num1,
  input logic [7:0] num2,
  input logic [1:0] op,
  input logic [7:0] result
);

  // Combinational logic: result is calculated based on num1, num2, and op
  // Ensure that the result is correctly calculated for each operation
  comb_result: assert property (
    @(posedge CLK) disable iff (!RESETn) (op == 2'b00) |-> (result == num1 + num2)
  );
  comb_result_sub: assert property (
    @(posedge CLK) disable iff (!RESETn) (op == 2'b01) |-> (result == num1 - num2)
  );
  comb_result_mul: assert property (
    @(posedge CLK) disable iff (!RESETn) (op == 2'b10) |-> (result == num1 * num2)
  );
  comb_result_div: assert property (
    @(posedge CLK) disable iff (!RESETn) (op == 2'b11) |-> (result == num1 / num2)
  );

endmodule