// SVA for TBUFX2
// Binds to DUT and checks functional equivalence, knownness, and provides compact coverage.

`ifndef TBUFX2_SVA
`define TBUFX2_SVA

module TBUFX2_sva (
  input logic [1:0] A,
  input logic       OE,
  input logic [3:0] Y
);

  // Functional equivalence (race-safe with #0)
  always_comb begin
    assert #0 (Y === (OE ? {A, ~A} : 4'b0))
      else $error("TBUFX2 SVA: Y mismatch. OE=%b A=%b Y=%b exp=%b",
                  OE, A, Y, (OE ? {A, ~A} : 4'b0));
  end

  // If inputs are fully known, outputs must be fully known
  assert property (@(A or OE or Y) (!$isunknown({A,OE})) |-> (!$isunknown(Y)))
    else $error("TBUFX2 SVA: Y has X/Z while inputs known. OE=%b A=%b Y=%b", OE, A, Y);

  // OE low forces zero regardless of A (checks 4-state exactness)
  assert property (@(A or OE or Y) (OE === 1'b0) |-> (Y === 4'b0000))
    else $error("TBUFX2 SVA: OE==0 but Y!=0. A=%b Y=%b", A, Y);

  // Minimal functional coverage
  cover property (@(A or OE) (OE===1'b0 && Y===4'b0000));
  cover property (@(A or OE) (OE===1'b1 && A==2'b00 && Y===4'b0011));
  cover property (@(A or OE) (OE===1'b1 && A==2'b01 && Y===4'b0110));
  cover property (@(A or OE) (OE===1'b1 && A==2'b10 && Y===4'b1001));
  cover property (@(A or OE) (OE===1'b1 && A==2'b11 && Y===4'b1100));
  cover property (@(posedge OE) 1);
  cover property (@(negedge OE) 1);

endmodule

bind TBUFX2 TBUFX2_sva sva_TBUFX2 (.*);

`endif