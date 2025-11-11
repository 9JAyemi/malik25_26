// SVA checker for add4; bind to DUT
module add4_sva(
  input logic [3:0] A, B,
  input logic [3:0] S,
  input logic       Cout
);

  // Combinational functional checks (immediate assertions)
  always_comb begin
    bit in_known = !$isunknown({A,B});
    bit out_known = !$isunknown({S,Cout});

    if (in_known) begin
      assert ({Cout,S} == A + B)
        else $error("add4: mismatch A=%0h B=%0h -> Cout=%0b S=%0h, exp Cout=%0b S=%0h",
                    A,B,Cout,S,(A+B)[4],(A+B)[3:0]);

      assert (out_known)
        else $error("add4: unknown outputs for known inputs A=%0h B=%0h", A, B);

      assert (Cout == ((A + B) > 4'hF))
        else $error("add4: carry incorrect A=%0h B=%0h Cout=%0b exp %0b",
                    A,B,Cout, ((A+B)>4'hF));

      if (A == 4'h0)
        assert (S == B && Cout == 1'b0)
          else $error("add4: A==0 identity failed B=%0h -> Cout=%0b S=%0h", B, Cout, S);

      if (B == 4'h0)
        assert (S == A && Cout == 1'b0)
          else $error("add4: B==0 identity failed A=%0h -> Cout=%0b S=%0h", A, Cout, S);
    end

    if ($isunknown({S,Cout})) begin
      assert ($isunknown({A,B}))
        else $error("add4: unknown outputs with known inputs A=%0h B=%0h", A, B);
    end
  end

  // Key scenario coverage (SVA cover)
  cover property ( !$isunknown({A,B}) && (A==4'h0 && B==4'h0) );   // zero+zero
  cover property ( !$isunknown({A,B}) && (A==4'hF && B==4'h1) );   // overflow boundary
  cover property ( !$isunknown({A,B}) && (A==4'h8 && B==4'h8) );   // mid+mid overflow
  cover property ( !$isunknown({A,B}) && (A==4'hF && B==4'h0) );   // max+zero
  cover property ( !$isunknown({A,B}) && (Cout==1'b1) );           // any carry
  cover property ( !$isunknown({A,B}) && (Cout==1'b0) );           // no carry

  // Full stimulus/output coverage (concise covergroup)
  covergroup cg_add4 @(A or B);
    cp_A    : coverpoint A { bins all[] = {[0:15]}; }
    cp_B    : coverpoint B { bins all[] = {[0:15]}; }
    cross_A_B : cross cp_A, cp_B;                 // all 256 input combinations
    cp_S    : coverpoint S { bins all[] = {[0:15]}; }
    cp_Cout : coverpoint Cout { bins zero = {0}; bins one = {1}; }
  endgroup
  cg_add4 cg = new;

endmodule

bind add4 add4_sva u_add4_sva(.A(A), .B(B), .S(S), .Cout(Cout));