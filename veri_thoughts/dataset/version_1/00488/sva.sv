// SVA checker for sky130_fd_sc_hdll__nand4bb
module sky130_fd_sc_hdll__nand4bb_sva (
  input A_N, input B_N, input C, input D,
  input VPWR, input VGND, input VPB, input VNB,
  input Y
);
  // Sample on any data input edge
  default clocking cb @(
    posedge A_N or negedge A_N or
    posedge B_N or negedge B_N or
    posedge C   or negedge C   or
    posedge D   or negedge D
  ); endclocking

  // Power-good gating
  wire pg = (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);
  default disable iff (!pg)

  // Functional equivalence (NOR of all four inputs)
  a_func: assert property (Y === ~(|{A_N,B_N,C,D})));

  // Bidirectional implications (redundant but pinpointing)
  a_hi_only_if_all_zero: assert property (Y |-> {A_N,B_N,C,D}==4'b0000);
  a_all_zero_implies_hi: assert property (({A_N,B_N,C,D}==4'b0000) |-> Y);

  // No X/Z on inputs and output when powered
  a_no_x_in : assert property (!$isunknown({A_N,B_N,C,D}));
  a_no_x_out: assert property (!$isunknown(Y));

  // Coverage: observe Y toggles and all 16 input combinations
  c_y_rose: cover property ($rose(Y));
  c_y_fell: cover property ($fell(Y));
  genvar i;
  generate
    for (i=0; i<16; i++) begin: g_cov
      cover property ({A_N,B_N,C,D} == i[3:0]);
    end
  endgenerate
endmodule

// Bind into DUT
bind sky130_fd_sc_hdll__nand4bb sky130_fd_sc_hdll__nand4bb_sva u_sva (.*);