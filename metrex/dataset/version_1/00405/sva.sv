// SVA bind module for binary_addition
// Concise checks for arithmetic, flags, saturation; plus minimal functional coverage.
`ifndef BINARY_ADDITION_SVA
`define BINARY_ADDITION_SVA

module binary_addition_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       C,   // 0:add, 1:sub
  input logic [3:0] S,
  input logic       OV,
  input logic       UF
);
  logic [4:0] add5, sub5;
  always_comb begin
    add5 = {1'b0, A} + {1'b0, B};
    sub5 = {1'b0, A} - {1'b0, B};

    // Basic sanity
    assert (!$isunknown({S, OV, UF})) else $error("binary_addition: X/Z on outputs");
    assert (!(OV && UF))              else $error("binary_addition: OV and UF both high");

    // Add path (C==0): OV == carry-out; UF must be 0; S either sum or zero on flag
    if (C == 1'b0) begin
      assert (OV == add5[4])         else $error("binary_addition: OV add mismatch");
      assert (UF == 1'b0)            else $error("binary_addition: UF must be 0 on add");
      if (OV || UF)  assert (S == 4'h0)      else $error("binary_addition: S must be 0 on flag (add)");
      else           assert (S == add5[3:0]) else $error("binary_addition: S != A+B");
    end
    // Sub path (C==1): OV follows borrow (as-coded); UF stuck-low; S either diff or zero on flag
    else begin
      assert (OV == sub5[4])         else $error("binary_addition: OV sub mismatch (borrow)");
      assert (UF == 1'b0)            else $error("binary_addition: UF must be 0 on sub (as-coded)");
      if (OV || UF)  assert (S == 4'h0)      else $error("binary_addition: S must be 0 on flag (sub)");
      else           assert (S == sub5[3:0]) else $error("binary_addition: S != A-B");
    end
  end

  // Minimal functional coverage
  always_comb begin
    cover (C == 1'b0 && add5[4] == 1'b0); // add, no carry
    cover (C == 1'b0 && add5[4] == 1'b1); // add, carry/overflow
    cover (C == 1'b1 && sub5[4] == 1'b0); // sub, no borrow
    cover (C == 1'b1 && sub5[4] == 1'b1); // sub, borrow/underflow
    cover (UF == 1'b1);                   // unreachable with current RTL (highlights bug)
  end
endmodule

bind binary_addition binary_addition_sva ba_sva (
  .A(A), .B(B), .C(C), .S(S), .OV(OV), .UF(UF)
);

`endif