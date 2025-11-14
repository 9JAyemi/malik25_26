// SVA checker and bind for adder_4bit
module adder_4bit_sva(
  input logic [3:0] A,
  input logic [3:0] B,
  input logic [3:0] S,
  input logic       Cout
);
  // Use global sampling event to enable concurrent SVA without a DUT clock
  default clocking cb @ (posedge $global_clock); endclocking

  // Functional correctness
  assert property ({Cout, S} == A + B)
    else $error("Adder mismatch: A=%0h B=%0h -> got Cout=%0b S=%0h", A, B, Cout, S);

  // Outputs never X/Z when inputs are known
  assert property (!$isunknown({A,B})) |-> !$isunknown({Cout,S})
    else $error("Unknown on outputs with known inputs: A=%0h B=%0h Cout=%b S=%0h", A, B, Cout, S);

  // Combinational stability (no output change without input change)
  assert property ($stable({A,B})) |=> $stable({Cout,S}))
    else $error("Outputs changed without input change");

  // 5-bit result range (max 30 for 4b+4b)
  assert property ({Cout,S} <= 5'd30)
    else $error("Result out of range: Cout=%0b S=%0h", Cout, S);

  // Coverage: carry cases and key corners
  cover property (Cout == 0);
  cover property (Cout == 1);
  cover property (A==4'h0 && B==4'h0 && S==4'h0 && Cout==1'b0);
  cover property (A==4'hF && B==4'h0 && S==4'hF && Cout==1'b0);
  cover property (A==4'hF && B==4'h1 && S==4'h0 && Cout==1'b1);
  cover property (A==4'hF && B==4'hF && S==4'hE && Cout==1'b1);

  // Full input-space coverage + result-space coverage
  covergroup cg_adder @(cb);
    coverpoint A { bins all[] = {[0:15]}; }
    coverpoint B { bins all[] = {[0:15]}; }
    A_x_B: cross A, B;

    coverpoint {Cout, S} {
      bins sum_vals[] = {[0:30]};
      illegal_bins impossible = {5'd31};
    }
  endgroup
  cg_adder cg = new();
endmodule

bind adder_4bit adder_4bit_sva sva_inst(.A(A), .B(B), .S(S), .Cout(Cout));