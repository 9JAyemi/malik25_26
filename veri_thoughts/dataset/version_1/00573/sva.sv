// SVA checker for sky130_fd_sc_hd__nor4b
module sky130_fd_sc_hd__nor4b_sva (
    input Y, A, B, C, D_N,
    input VPWR, VGND, VPB, VNB
);

  // Power-good and function
  wire pwr_good = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);
  wire [3:0] in = {A,B,C,D_N};
  wire y_func = ~(A | B | C | D_N);

  // Well ties
  assert property (@(*) VPB === VPWR);
  assert property (@(*) VNB === VGND);

  // Functional correctness when powered and inputs known
  always_comb begin
    if (pwr_good && !$isunknown(in)) assert #0 (Y === y_func);
  end

  // Safe 4-state implications (power-good)
  assert property (@(*) pwr_good && (A===1 || B===1 || C===1 || D_N===1) |-> (Y===1'b0));
  assert property (@(*) pwr_good && (A===0 && B===0 && C===0 && D_N===0) |-> (Y===1'b1));
  assert property (@(*) pwr_good && (Y===1'b1) |-> (A===0 && B===0 && C===0 && D_N===0));
  assert property (@(*) pwr_good && (Y===1'b0) |-> (A===1 || B===1 || C===1 || D_N===1));

  // Zero-delay response on known input changes
  assert property (@(*) (pwr_good && !$isunknown(in) && $changed(in)) |-> ##0 (Y === y_func));

  // Coverage
  cover property (@(*) pwr_good);
  cover property (@(*) pwr_good && (Y===1));
  cover property (@(*) pwr_good && (Y===0));
  cover property (@(*) pwr_good && (A===0 && B===0 && C===0 && D_N===0) && (Y===1));
  cover property (@(*) pwr_good && (A===1 && B===0 && C===0 && D_N===0) && (Y===0));
  cover property (@(*) pwr_good && (A===0 && B===1 && C===0 && D_N===0) && (Y===0));
  cover property (@(*) pwr_good && (A===0 && B===0 && C===1 && D_N===0) && (Y===0));
  cover property (@(*) pwr_good && (A===0 && B===0 && C===0 && D_N===1) && (Y===0));

endmodule

// Bind to all instances of the DUT
bind sky130_fd_sc_hd__nor4b sky130_fd_sc_hd__nor4b_sva sva_i (.*);