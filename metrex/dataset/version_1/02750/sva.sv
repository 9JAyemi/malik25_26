// Bind this SVA module to the DUT type
bind sky130_fd_sc_hd__nand4 sky130_fd_sc_hd__nand4_sva nand4_sva_inst();

module sky130_fd_sc_hd__nand4_sva;

  // Functional equivalence (4-state accurate)
  property p_func_equiv;
    @(A or B or C or D or Y) Y === ~(A & B & C & D);
  endproperty
  assert property (p_func_equiv);

  // Controlling-0 checks (any 0 forces Y=1 even with X/Z on others)
  assert property (@(A or B or C or D or Y) (A===1'b0) |-> (Y===1'b1));
  assert property (@(A or B or C or D or Y) (B===1'b0) |-> (Y===1'b1));
  assert property (@(A or B or C or D or Y) (C===1'b0) |-> (Y===1'b1));
  assert property (@(A or B or C or D or Y) (D===1'b0) |-> (Y===1'b1));

  // All-ones case -> Y=0
  assert property (@(A or B or C or D or Y)
                   (A===1'b1 && B===1'b1 && C===1'b1 && D===1'b1) |-> (Y===1'b0));

  // X/Z propagation when no input is 0 and not all are 1
  assert property (@(A or B or C or D or Y)
                   (A!==1'b0 && B!==1'b0 && C!==1'b0 && D!==1'b0 &&
                    !(A===1'b1 && B===1'b1 && C===1'b1 && D===1'b1)) |-> (Y===1'bx));

  // No-Z on output (buffer must drive)
  assert property (@(A or B or C or D or Y) (Y !== 1'bz));

  // If all inputs are known, output must be known
  assert property (@(A or B or C or D or Y) (!$isunknown({A,B,C,D})) |-> !$isunknown(Y));

  // Buffer integrity (internal net equals output)
  assert property (@(A or B or C or D or Y) Y === nand0_out_Y);

  // Power pins sanity (as modeled)
  assert property (@(A or B or C or D or Y)
                   (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0));

  // Functional coverage: cover all 16 known input combinations and expected Y
  cover property (@(A or B or C or D or Y) (A===0 && B===0 && C===0 && D===0 && Y===1));
  cover property (@(A or B or C or D or Y) (A===0 && B===0 && C===0 && D===1 && Y===1));
  cover property (@(A or B or C or D or Y) (A===0 && B===0 && C===1 && D===0 && Y===1));
  cover property (@(A or B or C or D or Y) (A===0 && B===0 && C===1 && D===1 && Y===1));
  cover property (@(A or B or C or D or Y) (A===0 && B===1 && C===0 && D===0 && Y===1));
  cover property (@(A or B or C or D or Y) (A===0 && B===1 && C===0 && D===1 && Y===1));
  cover property (@(A or B or C or D or Y) (A===0 && B===1 && C===1 && D===0 && Y===1));
  cover property (@(A or B or C or D or Y) (A===0 && B===1 && C===1 && D===1 && Y===1));
  cover property (@(A or B or C or D or Y) (A===1 && B===0 && C===0 && D===0 && Y===1));
  cover property (@(A or B or C or D or Y) (A===1 && B===0 && C===0 && D===1 && Y===1));
  cover property (@(A or B or C or D or Y) (A===1 && B===0 && C===1 && D===0 && Y===1));
  cover property (@(A or B or C or D or Y) (A===1 && B===0 && C===1 && D===1 && Y===1));
  cover property (@(A or B or C or D or Y) (A===1 && B===1 && C===0 && D===0 && Y===1));
  cover property (@(A or B or C or D or Y) (A===1 && B===1 && C===0 && D===1 && Y===1));
  cover property (@(A or B or C or D or Y) (A===1 && B===1 && C===1 && D===0 && Y===1));
  cover property (@(A or B or C or D or Y) (A===1 && B===1 && C===1 && D===1 && Y===0));

  // Coverage for X/Z propagation scenario
  cover property (@(A or B or C or D or Y)
                  (A!==1'b0 && B!==1'b0 && C!==1'b0 && D!==1'b0 &&
                   !(A===1'b1 && B===1'b1 && C===1'b1 && D===1'b1) && Y===1'bx));

endmodule