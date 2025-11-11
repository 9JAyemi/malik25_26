// SVA checker for 1-bit full adders with power pins.
// Binds to both binary_adder and fah. Uses immediate asserts and cover properties.
module fa_sva (
  input logic A, B, CI,
  input logic SUM, COUT,
  input logic VPWR, VGND
);

  // Power-good qualification
  function automatic bit pgood;
    return (VPWR === 1'b1) && (VGND === 1'b0);
  endfunction

  // Functional equivalence and X-checks under valid power and known inputs
  always @* begin
    if (pgood() && !$isunknown({A,B,CI})) begin
      assert ({COUT,SUM} === (A + B + CI))
        else $error("FA func mismatch: {COUT,SUM} != A+B+CI (A=%0b B=%0b CI=%0b SUM=%0b COUT=%0b)", A,B,CI,SUM,COUT);
      assert (!$isunknown({SUM,COUT}))
        else $error("FA outputs unknown with known inputs and valid power");
      // Cross-check carry with majority-of-three identity
      assert (COUT === ((A & B) | (A & CI) | (B & CI)))
        else $error("Carry identity mismatch");
    end
  end

  // Functional coverage: all input combinations under valid power
  cover property (@(A or B or CI or VPWR or VGND) pgood() && {A,B,CI} == 3'b000);
  cover property (@(A or B or CI or VPWR or VGND) pgood() && {A,B,CI} == 3'b001);
  cover property (@(A or B or CI or VPWR or VGND) pgood() && {A,B,CI} == 3'b010);
  cover property (@(A or B or CI or VPWR or VGND) pgood() && {A,B,CI} == 3'b011);
  cover property (@(A or B or CI or VPWR or VGND) pgood() && {A,B,CI} == 3'b100);
  cover property (@(A or B or CI or VPWR or VGND) pgood() && {A,B,CI} == 3'b101);
  cover property (@(A or B or CI or VPWR or VGND) pgood() && {A,B,CI} == 3'b110);
  cover property (@(A or B or CI or VPWR or VGND) pgood() && {A,B,CI} == 3'b111);

  // Optional: observe that power-good occurs at least once
  cover property (@(VPWR or VGND) (VPWR === 1'b1) && (VGND === 1'b0));

endmodule

// Bind the checker to both DUTs
bind binary_adder fa_sva u_fa_sva_binary_adder (.A(A),.B(B),.CI(CI),.SUM(SUM),.COUT(COUT),.VPWR(VPWR),.VGND(VGND));
bind fah          fa_sva u_fa_sva_fah          (.A(A),.B(B),.CI(CI),.SUM(SUM),.COUT(COUT),.VPWR(VPWR),.VGND(VGND));