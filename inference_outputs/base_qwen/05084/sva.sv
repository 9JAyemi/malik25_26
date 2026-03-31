```systemverilog
module adder4_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic CIN,
  output logic [3:0] S,
  output logic COUT
);
  // Combinational logic, so use @(posedge clk)
  
  // Sum calculation is correct
  sum_correct: assert property (
    @(posedge clk) disable iff (!reset_n) (S == A + B + CIN)
  );
  
  // COUT is the carry out bit of the sum
  carry_out_correct: assert property (
    @(posedge clk) disable iff (!reset_n) (COUT == sum[4])
  );
  
  // S is the lower 4 bits of the sum
  sum_bits_correct: assert property (
    @(posedge clk) disable iff (!reset_n) (S == sum[3:0])
  );
  
  // CIN is used in the sum calculation
  cin_used: assert property (
    @(posedge clk) disable iff (!reset_n) (COUT == (A + B + CIN)[4])
  );
  
  // S is not greater than 4 bits
  sum_not_overflow: assert property (
    @(posedge clk) disable iff (!reset_n) (S < 4'b10000)
  );
  
  // COUT is either 0 or 1
  carry_out_valid: assert property (
    @(posedge clk) disable iff (!reset_n) (COUT inside {0, 1})
  );
  
  // S is not less than 0
  sum_not_underflow: assert property (
    @(posedge clk) disable iff (!reset_n) (S >= 4'b0)
  );
  
  // CIN is either 0 or 1
  cin_valid: assert property (
    @(posedge clk) disable iff (!reset_n) (CIN inside {0, 1})
  );
  
  // A is not greater than 4 bits
  a_valid: assert property (
    @(posedge clk) disable iff (!reset_n) (A < 4'b10000)
  );
  
  // B is not greater than 4 bits
  b_valid: assert property (
    @(posedge clk) disable iff (!reset_n) (B < 4'b10000)
  );
  
endmodule
```