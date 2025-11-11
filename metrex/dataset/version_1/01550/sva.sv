// SVA checker for add4bit
checker add4bit_sva(
  input logic        clk,
  input logic        rst_n,
  input logic [3:0]  A, B, C, D,
  input logic [4:0]  sum
);
  default clocking @(posedge clk); endclocking

  // 6-bit true total and expected DUT output (mod-16, MSB forced 0)
  let tot6 = {2'b0,A} + {2'b0,B} + {2'b0,C} + {2'b0,D};
  let exp5 = {1'b0, tot6[3:0]};

  // Functional correctness (when inputs are known) + no-X on sum
  a_func: assert property (disable iff (!rst_n)
                           !$isunknown({A,B,C,D}) |-> (sum == exp5 && !$isunknown(sum)))
          else $error("add4bit mismatch: exp=%0d got=%0d (A=%0d B=%0d C=%0d D=%0d)",
                      exp5, sum, A, B, C, D);

  // Output MSB must always be 0 and sum must be in 0..15
  a_msb0:   assert property (disable iff (!rst_n) sum[4] == 1'b0);
  a_range:  assert property (disable iff (!rst_n) sum inside {[5'd0:5'd15]});

  // Key functional coverage (edges and overflow cases)
  c_zero:       cover property (tot6 == 0   && sum == 5'd0);
  c_one:        cover property (tot6 == 1   && sum == 5'd1);
  c_15:         cover property (tot6 == 15  && sum == 5'd15);
  c_16_wrap:    cover property (tot6 == 16  && sum == 5'd0);
  c_31_wrap:    cover property (tot6 == 31  && sum == 5'd15);
  c_60_wrap:    cover property (tot6 == 60  && sum == 5'd12);
  c_overflow:   cover property (tot6 >= 16);
endchecker

// Bind example (provide a free-running clk; tie rst_n high if no reset)
// bind add4bit add4bit_sva u_add4bit_sva(.clk(clk), .rst_n(1'b1), .A(A), .B(B), .C(C), .D(D), .sum(sum));