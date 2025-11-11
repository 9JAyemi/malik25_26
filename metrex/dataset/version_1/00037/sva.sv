// SVA checker for binary_adder
// Concise, combinational, bind-ready. Uses immediate assertions for delta-cycle settle.

module binary_adder_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       Cin,
  input logic [3:0] S,
  input logic       Cout
);

  // Combinational reference model
  logic [4:0] ref_sum;
  always_comb ref_sum = A + B + Cin;

  // X/Z checks (inputs and outputs)
  always_comb begin
    assert (!$isunknown({A,B,Cin})) else $error("binary_adder: X/Z on inputs A/B/Cin");
    assert (!$isunknown({S,Cout}))  else $error("binary_adder: X/Z on outputs S/Cout");
  end

  // Functional equivalence: outputs equal full 5-bit sum (allow delta via #0)
  always_comb begin
    assert #0 ({Cout,S} === ref_sum)
      else $error("binary_adder: {Cout,S} != A+B+Cin. A=%0h B=%0h Cin=%0b S=%0h Cout=%0b ref=%0h",
                  A,B,Cin,S,Cout,ref_sum);
  end

  // Minimal but meaningful functional coverage
  // Note: immediate cover samples whenever combinationally active.
  always_comb begin
    cover ({Cout,S} === ref_sum);                  // basic functional activation
    cover (!Cout);                                 // no carry-out
    cover ( Cout);                                 // carry-out occurred
    cover (!Cin && Cout);                          // carry from A+B only
    cover ( Cin && Cout);                          // carry due to Cin contribution
    cover (A==4'h0 && B==4'h0 && Cin==1'b0 &&
           S==4'h0 && Cout==1'b0);                 // lowest corner
    cover (A==4'hF && B==4'hF && Cin==1'b1 &&
           S==4'hF && Cout==1'b1);                 // highest corner (31 -> 1F)
  end

endmodule

// Bind into the DUT
bind binary_adder binary_adder_sva u_binary_adder_sva (
  .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout)
);