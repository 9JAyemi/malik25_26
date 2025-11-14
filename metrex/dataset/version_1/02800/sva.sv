// SVA for sky130_fd_sc_ls__fahcin (full adder, active-low CIN)

module sky130_fd_sc_ls__fahcin_sva (
  input  logic A,
  input  logic B,
  input  logic CIN,   // active-low carry-in
  input  logic SUM,
  input  logic COUT
);

  // Core functional checks (guarded against X/Z on inputs)
  always_comb begin
    if (!$isunknown({A,B,CIN})) begin
      assert ({COUT,SUM} == (A + B + (~CIN)))
        else $error("FA functional mismatch: {COUT,SUM} != A+B+~CIN (A=%0b B=%0b CIN=%0b SUM=%0b COUT=%0b)", A,B,CIN,SUM,COUT);

      assert (SUM == (A ^ B ^ ~CIN))
        else $error("SUM mismatch: expected A^B^~CIN (A=%0b B=%0b CIN=%0b SUM=%0b)", A,B,CIN,SUM);

      assert (COUT == ((A & B) | (A & ~CIN) | (B & ~CIN)))
        else $error("COUT mismatch: expected AB + A~CIN + B~CIN (A=%0b B=%0b CIN=%0b COUT=%0b)", A,B,CIN,COUT);

      // Mode-specific simplifications (useful for debug)
      assert ((CIN == 1'b1) -> (SUM == (A ^ B) && COUT == (A & B)))
        else $error("CIN=1 mode mismatch: SUM should be A^B and COUT A&B (A=%0b B=%0b)", A,B);

      assert ((CIN == 1'b0) -> (SUM == ~(A ^ B) && COUT == (A | B)))
        else $error("CIN=0 mode mismatch: SUM should be ~(A^B) and COUT A|B (A=%0b B=%0b)", A,B);

      // No X/Z on outputs when inputs are known
      assert (!$isunknown({SUM,COUT}))
        else $error("Outputs contain X/Z with known inputs (SUM=%0b COUT=%0b)", SUM, COUT);
    end
  end

  // Minimal but complete input-space coverage (all 8 combinations)
  always_comb begin
    cover ({A,B,CIN} == 3'b000);
    cover ({A,B,CIN} == 3'b001);
    cover ({A,B,CIN} == 3'b010);
    cover ({A,B,CIN} == 3'b011);
    cover ({A,B,CIN} == 3'b100);
    cover ({A,B,CIN} == 3'b101);
    cover ({A,B,CIN} == 3'b110);
    cover ({A,B,CIN} == 3'b111);
  end

  // Output value coverage (ensures both polarities are observed)
  always_comb begin
    cover (SUM  == 1'b0); cover (SUM  == 1'b1);
    cover (COUT == 1'b0); cover (COUT == 1'b1);
  end

endmodule

// Bind into the DUT
bind sky130_fd_sc_ls__fahcin sky130_fd_sc_ls__fahcin_sva u_fahcin_sva (
  .A(A), .B(B), .CIN(CIN), .SUM(SUM), .COUT(COUT)
);