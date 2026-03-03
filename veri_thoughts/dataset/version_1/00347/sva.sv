// SVA for binary_adder
module binary_adder_sva (
  input logic [7:0] A,
  input logic [7:0] B,
  input logic       C,
  input logic [7:0] S
);
  logic [8:0] add9, sub9;
  logic [7:0] expS;

  always_comb begin
    add9 = {1'b0, A} + {1'b0, B};
    sub9 = {1'b0, A} - {1'b0, B};
    expS = C ? sub9[7:0] : add9[7:0];

    // Functional correctness and X-prop (sample after comb settles)
    if (!$isunknown({A,B,C})) begin
      assert #0 (S === expS)
        else $error("binary_adder mismatch: C=%0b A=%0h B=%0h S=%0h exp=%0h", C,A,B,S,expS);
      assert #0 (!$isunknown(S))
        else $error("binary_adder X/Z on S with known inputs: C=%0b A=%0h B=%0h S=%0h", C,A,B,S);
    end

    // Concise functional coverage (key modes and corner cases)
    cover #0 (C==1'b0);                    // add mode hit
    cover #0 (C==1'b1);                    // sub mode hit
    cover #0 (C==1'b0 && add9[8]);         // add overflow
    cover #0 (C==1'b1 && (A < B));         // sub underflow (borrow)
    cover #0 (A==8'h00 && B==8'h00);       // both zero
    cover #0 (A==8'hFF && B==8'h00);
    cover #0 (A==8'h00 && B==8'hFF);
    cover #0 (A==8'hFF && B==8'hFF);       // max - max / max + max
    cover #0 (C==1'b0 && S==8'h00);        // zero sum
    cover #0 (C==1'b1 && S==8'h00);        // zero diff
  end
endmodule

bind binary_adder binary_adder_sva sva_inst(.A(A), .B(B), .C(C), .S(S));