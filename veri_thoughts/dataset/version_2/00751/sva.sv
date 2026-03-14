module ripple_carry_adder_sva (
  input logic clk,
  input logic [3:0] A,
  input logic [3:0] B,
  input logic Cin,
  input logic [3:0] S,
  input logic Cout
);

  ///// Registered behaviors /////
  // S registers the lower 4 bits of A+B+Cin from the previous cycle.
  check_sum_registered: assert property (
    @(posedge clk) S == $past((A + B + Cin)[3:0])
  );

  // Cout registers the MSB carry expression from the previous cycle.
  check_cout_registered: assert property (
    @(posedge clk) Cout == $past((A[3] & B[3]) | (A[3] & Cin) | (B[3] & Cin))
  );

  ///// Stability with repeated inputs /////
  // If A,B,Cin are identical across the last two cycles, outputs repeat.
  check_outputs_repeat_when_inputs_repeat: assert property (
    @(posedge clk) ($past(A,1) == $past(A,2)) && ($past(B,1) == $past(B,2)) && ($past(Cin,1) == $past(Cin,2))
      |-> (S == $past(S)) && (Cout == $past(Cout))
  );

  ///// Sum corner cases /////
  // With B=0 and Cin=0, S follows A (one-cycle latency).
  check_S_eq_A_when_B0_Cin0: assert property (
    @(posedge clk) ($past(B) == 4'b0000) && ($past(Cin) == 1'b0) |-> (S == $past(A))
  );

  // With A=0 and Cin=0, S follows B (one-cycle latency).
  check_S_eq_B_when_A0_Cin0: assert property (
    @(posedge clk) ($past(A) == 4'b0000) && ($past(Cin) == 1'b0) |-> (S == $past(B))
  );

  // With A=0, B=0, Cin=0, S is 0 (one-cycle latency).
  check_S_zero_when_all_zero: assert property (
    @(posedge clk) ($past(A) == 4'b0000) && ($past(B) == 4'b0000) && ($past(Cin) == 1'b0) |-> (S == 4'b0000)
  );

  // With A=0, B=0, Cin=1, S is 1 (one-cycle latency).
  check_S_one_when_only_Cin1: assert property (
    @(posedge clk) ($past(A) == 4'b0000) && ($past(B) == 4'b0000) && ($past(Cin) == 1'b1) |-> (S == 4'b0001)
  );

  // With A=0xF, B=0, Cin=1, S wraps to 0 (one-cycle latency).
  check_S_zero_when_A_F_B0_Cin1: assert property (
    @(posedge clk) ($past(A) == 4'hF) && ($past(B) == 4'h0) && ($past(Cin) == 1'b1) |-> (S == 4'h0)
  );

  ///// Cout corner cases /////
  // If A[3] and B[3] are 1, Cout is 1 (one-cycle latency).
  check_Cout_one_when_A3_and_B3: assert property (
    @(posedge clk) $past(A[3]) && $past(B[3]) |-> (Cout == 1'b1)
  );

  // If Cin=1 and either A[3] or B[3] is 1, Cout is 1 (one-cycle latency).
  check_Cout_one_when_Cin1_and_MSB_one: assert property (
    @(posedge clk) $past(Cin) && ($past(A[3]) || $past(B[3])) |-> (Cout == 1'b1)
  );

  // If Cin=0 and exactly one of A[3],B[3] is 1, Cout is 0 (one-cycle latency).
  check_Cout_zero_when_Cin0_onehot_MSB: assert property (
    @(posedge clk) !$past(Cin) && ($past(A[3]) ^ $past(B[3])) |-> (Cout == 1'b0)
  );

  // If A[3]=0, B[3]=0, and Cin=1, Cout is 0 (one-cycle latency).
  check_Cout_zero_when_no_MSB_and_Cin1: assert property (
    @(posedge clk) !$past(A[3]) && !$past(B[3]) && $past(Cin) |-> (Cout == 1'b0)
  );

endmodule