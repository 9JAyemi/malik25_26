// SVA for four_bit_adder
// Focus: functional correctness, X-propagation checks, key scenario coverage

module four_bit_adder_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] Sum,
  input  logic       Cout
);

  // Helper: expected 5-bit result
  function automatic logic [4:0] exp5();
    exp5 = A + B + Cin; // SV sizes this to 5 bits
  endfunction

  // Outputs known after inputs change
  assert property (@(A or B or Cin) ##0 !$isunknown({Sum, Cout}))
    else $error("four_bit_adder: X/Z detected on outputs");

  // Core functional check: {Cout,Sum} must equal 5-bit sum of inputs
  assert property (@(A or B or Cin) ##0 {Cout, Sum} == exp5())
    else $error("four_bit_adder: wrong result: A=%0h B=%0h Cin=%0b -> got {Cout,Sum}=%0h expected %0h",
                A, B, Cin, {Cout,Sum}, exp5());

  // Minimal, high-value coverage
  // Carry vs no-carry
  cover property (@(A or B or Cin) ((A + B + Cin) <= 4'hF));
  cover property (@(A or B or Cin) ((A + B + Cin) >  4'hF));

  // Corners
  cover property (@(A or B or Cin) (A==4'h0 && B==4'h0 && Cin==0));
  cover property (@(A or B or Cin) (A==4'hF && B==4'hF && Cin==1)); // max overflow
  cover property (@(A or B or Cin) (A==4'hF && B==4'h0 && Cin==1)); // wraps to 0 with carry
  cover property (@(A or B or Cin) (A==4'h7 && B==4'h8 && Cin==0)); // boundary to 0xF

endmodule

// Bind into DUT
bind four_bit_adder four_bit_adder_sva sva_i (
  .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout)
);