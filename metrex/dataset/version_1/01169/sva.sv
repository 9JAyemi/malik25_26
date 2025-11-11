// SVA checker for binary_adder
module binary_adder_sva #(parameter W=4)
(
  input logic [W-1:0] A,
  input logic [W-1:0] B,
  input logic         C_in,
  input logic [W-1:0] S
);

  function automatic logic [W-1:0] sum4(input logic [W-1:0] a, b, input logic cin);
    logic [W:0] ext;
    begin
      ext  = a + b + cin;
      sum4 = ext[W-1:0];
    end
  endfunction

  function automatic logic carry_out(input logic [W-1:0] a, b, input logic cin);
    logic [W:0] ext;
    begin
      ext       = a + b + cin;
      carry_out = ext[W];
    end
  endfunction

  // Functional correctness and no-X on S when inputs are known; zero-delay settle
  property p_func;
    @(A or B or C_in) ##0 (!$isunknown({A,B,C_in})) |-> (! $isunknown(S) && S == sum4(A,B,C_in));
  endproperty
  assert property (p_func);

  // Pure combinational: S must not change unless inputs change (no spurious glitches)
  property p_pure_comb;
    @(A or B or C_in or S) ##0 $stable({A,B,C_in}) |-> $stable(S);
  endproperty
  assert property (p_pure_comb);

  // Coverage: exercise cin, carry/no-carry, and extreme sums
  cover property (@(A or B or C_in) ##0 C_in == 1'b0);
  cover property (@(A or B or C_in) ##0 C_in == 1'b1);
  cover property (@(A or B or C_in) ##0 carry_out(A,B,C_in) == 1'b0);
  cover property (@(A or B or C_in) ##0 carry_out(A,B,C_in) == 1'b1);
  cover property (@(A or B or C_in) ##0 S == '0);
  cover property (@(A or B or C_in) ##0 S == {W{1'b1}});
  // Wrap-around corner: max + 1 with cin=0 -> 0
  cover property (@(A or B or C_in) ##0
                  A == {W{1'b1}} && B == {{(W-1){1'b0}},1'b1} && C_in == 1'b0 && S == '0);

endmodule

// Bind into DUT
bind binary_adder binary_adder_sva #(.W(4)) u_binary_adder_sva (.A(A), .B(B), .C_in(C_in), .S(S));