module adder_4bit_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic cin,
  output logic [3:0] s,
  output logic cout
);
  // Combinational logic, clocked assertions
  // Sum calculation is correct
  sum_calculation: assert property (
    @(posedge clk) disable iff (!resetn) (s == (a + b + cin)[3:0])
  );
  // Carry out calculation is correct
  carry_out_calculation: assert property (
    @(posedge clk) disable iff (!resetn) (cout == (a + b + cin)[4])
  );
endmodule