// SVA for Modulo
// Bind-only, no DUT edits required

module Modulo_sva (
  input  logic [31:0] A,
  input  logic [31:0] B,
  input  logic [31:0] C
);

  // Golden-model of DUT behavior (mirrors RTL, guarded for B==0)
  function automatic logic [31:0] ref_mod (input logic [31:0] a, b);
    logic signed [31:0] temp;
    begin
      if (b == 32'd0) ref_mod = 32'd0;
      else begin
        temp = $signed(a % b);
        if (temp < 0) ref_mod = temp + b;
        else          ref_mod = temp;
      end
    end
  endfunction

  // Combinational equivalence to golden model
  always_comb begin
    assert (C === ref_mod(A,B))
      else $error("Modulo mismatch: A=%0h B=%0h C=%0h exp=%0h", A, B, C, ref_mod(A,B));
  end

  // No-X/Z on C when inputs are known
  assert property (@(A or B or C) !$isunknown({A,B}) |-> !$isunknown(C));

  // B==0 handling
  assert property (@(A or B or C) (B==32'd0) |-> (C==32'd0));

  // Simple corner: B==1 => C==0
  assert property (@(A or B or C) (B==32'd1) |-> (C==32'd0));

  // Safe-range check when B is strictly less than 2^31
  assert property (@(A or B or C) (B!=0 && B[31]==1'b0) |-> (C < B));

  // If B < 2^31 and A < B then C==A
  assert property (@(A or B or C) (B!=0 && B[31]==1'b0 && A < B) |-> (C==A));

  // Coverage: hit all control paths and key corners
  cover property (@(A or B) (B==32'd0));
  cover property (@(A or B) (B!=0 && $signed(A % B) < 0));   // negative-correction path
  cover property (@(A or B) (B!=0 && $signed(A % B) >= 0));  // direct path
  cover property (@(A or B) (B!=0 && (A % B)==0));           // exact multiple
  cover property (@(A or B) (B[31]==1'b1));                  // large B (MSB=1)
  cover property (@(A or B) (B!=0 && A < B));
  cover property (@(A or B) (B!=0 && A >= B));

endmodule

bind Modulo Modulo_sva u_modulo_sva (.A(A), .B(B), .C(C));