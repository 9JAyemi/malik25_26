// SVA checker for full_adder. Bind into the DUT to access internal C.
module full_adder_sva #(parameter W=8) (
  input logic [W-1:0] A,
  input logic [W-1:0] B,
  input logic [W:0]   S,
  input logic [W:0]   C   // bound to DUT internal carry chain
);
  // Ignore checks when inputs contain X/Z
  default disable iff ($isunknown({A,B}));

  // Sum correctness (9-bit add)
  assert property (@(A or B) 1'b1 |-> ##0 ( S === {1'b0,A} + {1'b0,B} ))
    else $error("SUM != A+B");

  // Output must be known if inputs are known
  assert property (@(A or B) !$isunknown({A,B}) |-> ##0 !$isunknown(S))
    else $error("S has X/Z for known inputs");

  // LSB stage (no carry-in)
  assert property (@(A or B) 1'b1 |-> ##0 ( S[0] == (A[0] ^ B[0]) ))
    else $error("S[0] wrong");
  assert property (@(A or B) 1'b1 |-> ##0 ( C[1] == (A[0] & B[0]) ))
    else $error("C[1] wrong");

  // Middle + last stages: sum and carry propagate/generate
  genvar i;
  generate
    for (i=1; i<=W-1; i++) begin : g_bit
      assert property (@(A or B) 1'b1 |-> ##0 ( S[i] == (A[i] ^ B[i] ^ C[i]) ))
        else $error("S[%0d] wrong", i);
      assert property (@(A or B) 1'b1 |-> ##0 ( C[i+1] == ((A[i]&B[i])|(A[i]&C[i])|(B[i]&C[i])) ))
        else $error("C[%0d] wrong", i+1);
    end
  endgenerate

  // MSB carry-out equals S[W]
  assert property (@(A or B) 1'b1 |-> ##0 ( S[W] == C[W] ))
    else $error("S[MSB] != carry-out");

  // Concise functional coverage of key scenarios
  cover property (@(A or B) (A==8'h00 && B==8'h00) ##0 (S==9'h000));  // zero+zero
  cover property (@(A or B) (A==8'hFF && B==8'h01) ##0 (S==9'h100));  // full ripple carry
  cover property (@(A or B) (A==8'hFF && B==8'hFF) ##0 (S==9'h1FE));  // max+max
  cover property (@(A or B) (A==8'h55 && B==8'hAA) ##0 (S==9'h0FF));  // no carries
  cover property (@(A or B) (A==8'h80 && B==8'h80) ##0 (S==9'h100));  // MSB carry only
endmodule

// Bind into the DUT (tooling allows connecting to internal nets on bind)
bind full_adder full_adder_sva #(.W(8)) u_full_adder_sva ( .A(A), .B(B), .S(S), .C(C) );