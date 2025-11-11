// SVA for sky130_fd_sc_lp__o2111ai (Y = ~(C1 & B1 & D1 & (A1 | A2)))
module o2111ai_sva;

  // Power rails sanity (constants in this macrocell)
  initial begin
    assert (VPWR === 1'b1);
    assert (VPB  === 1'b1);
    assert (VGND === 1'b0);
    assert (VNB  === 1'b0);
  end

  // Functional equivalence (4-state accurate)
  property p_func;
    @(A1 or A2 or B1 or C1 or D1 or Y)
      1'b1 |-> ##0 (Y === ~(C1 & B1 & D1 & (A1 | A2)));
  endproperty
  assert property (p_func);

  // Internal net correctness
  assert property (@(A1 or A2 or or0_out) 1'b1 |-> ##0 (or0_out === (A1 | A2)));
  assert property (@(or0_out or B1 or C1 or D1 or nand0_out_Y)
                   1'b1 |-> ##0 (nand0_out_Y === ~(C1 & B1 & D1 & or0_out)));
  assert property (@(nand0_out_Y or Y) 1'b1 |-> ##0 (Y === nand0_out_Y));

  // Tight implications (catch inconsistent X-resolutions)
  assert property (@(A1 or A2 or B1 or C1 or D1 or Y) (B1===1'b0) |-> (Y===1'b1));
  assert property (@(A1 or A2 or B1 or C1 or D1 or Y) (C1===1'b0) |-> (Y===1'b1));
  assert property (@(A1 or A2 or B1 or C1 or D1 or Y) (D1===1'b0) |-> (Y===1'b1));
  assert property (@(A1 or A2 or B1 or C1 or D1 or Y) ((A1===1'b0)&&(A2===1'b0)) |-> (Y===1'b1));

  assert property (@(A1 or A2 or B1 or C1 or D1 or Y)
                   (B1===1'b1 && C1===1'b1 && D1===1'b1 && (A1===1'b1 || A2===1'b1))
                   |-> (Y===1'b0));

  assert property (@(A1 or A2 or B1 or C1 or D1 or Y)
                   (Y===1'b0) |-> (B1===1'b1 && C1===1'b1 && D1===1'b1 && (A1===1'b1 || A2===1'b1)));
  assert property (@(A1 or A2 or B1 or C1 or D1 or Y)
                   (Y===1'b1) |-> (B1===1'b0 || C1===1'b0 || D1===1'b0 || (A1===1'b0 && A2===1'b0)));

  // Output never Z
  assert property (@(Y) Y !== 1'bz);

  // Key functional coverage
  cover property (@(A1 or A2 or B1 or C1 or D1 or Y)
                  (B1===1 && C1===1 && D1===1 && (A1===1 || A2===1) && Y===0));
  cover property (@(A1 or A2 or B1 or C1 or D1 or Y)
                  (B1===1 && C1===1 && D1===1 && A1===0 && A2===0 && Y===1));
  cover property (@(A1 or A2 or B1 or C1 or D1 or Y)
                  (B1===0 && C1===1 && D1===1 && Y===1));
  cover property (@(A1 or A2 or B1 or C1 or D1 or Y)
                  (B1===1 && C1===0 && D1===1 && Y===1));
  cover property (@(A1 or A2 or B1 or C1 or D1 or Y)
                  (B1===1 && C1===1 && D1===0 && Y===1));

  // X-propagation coverage through OR->AND->INV path
  cover property (@(A1 or A2 or B1 or C1 or D1 or Y)
                  (B1===1 && C1===1 && D1===1 &&
                   ((A1===1'bx && A2===1'b0) || (A2===1'bx && A1===1'b0)) &&
                   Y===1'bx));
endmodule

bind sky130_fd_sc_lp__o2111ai o2111ai_sva o2111ai_sva_i();