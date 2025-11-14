// SVA for four_bit_adder
module four_bit_adder_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] S
);

  // Functional correctness and X-prop
  always_comb begin
    bit known_in = !$isunknown({A,B,Cin});
    if (known_in) begin
      assert (!$isunknown(S))
        else $error("four_bit_adder: S has X/Z with known inputs");
      assert (S == (A + B + Cin)[3:0])
        else $error("four_bit_adder: wrong sum A=%0h B=%0h Cin=%0b S=%0h exp=%0h",
                    A, B, Cin, S, (A+B+Cin)[3:0]);
    end
  end

  // Compact yet meaningful functional coverage
  always_comb begin
    bit known_in = !$isunknown({A,B,Cin});
    cover (known_in && Cin==0);
    cover (known_in && Cin==1);
    cover (known_in && (A + B + Cin) < 16);     // no carry-out case
    cover (known_in && (A + B + Cin) >= 16);    // carry-out occurred
    cover (known_in && S == 4'h0);
    cover (known_in && S == 4'hF);
    cover (known_in && A==4'h0 && B==4'h0 && Cin==1'b0); // min corner
    cover (known_in && A==4'hF && B==4'hF && Cin==1'b1); // max corner
  end

endmodule

bind four_bit_adder four_bit_adder_sva sva_i(.A(A), .B(B), .Cin(Cin), .S(S));