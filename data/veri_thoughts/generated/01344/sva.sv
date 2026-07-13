module pairwise_xor_sva (
  // RTL has no clock/reset; this wrapper uses 'clk' only for SVA sampling.
  input logic clk,
  // DUT ports (observed as inputs here)
  input logic a,
  input logic b,
  input logic c,
  input logic d,
  input logic e,
  input logic [24:0] out
);

  // out equals the concatenation of all pairwise XORs as in the RTL.
  check_full_concat_mapping: assert property (
    @(posedge clk) out == {a^a, a^b, a^c, a^d, a^e, b^a, b^b, b^c, b^d, b^e, c^a, c^b, c^c, c^d, c^e, d^a, d^b, d^c, d^d, d^e, e^a, e^b, e^c, e^d, e^e}
  );

  ///// Diagonal bits (x^x) are zero /////
  // a^a bit is always 0.
  check_diagonal_aa_zero: assert property (
    @(posedge clk) out[24] == 1'b0
  );
  // b^b bit is always 0.
  check_diagonal_bb_zero: assert property (
    @(posedge clk) out[18] == 1'b0
  );
  // c^c bit is always 0.
  check_diagonal_cc_zero: assert property (
    @(posedge clk) out[12] == 1'b0
  );
  // d^d bit is always 0.
  check_diagonal_dd_zero: assert property (
    @(posedge clk) out[6] == 1'b0
  );
  // e^e bit is always 0.
  check_diagonal_ee_zero: assert property (
    @(posedge clk) out[0] == 1'b0
  );

  ///// Symmetry of XOR: x^y == y^x /////
  // a^b equals b^a.
  check_symmetry_ab_ba_equal: assert property (
    @(posedge clk) out[23] == out[19]
  );
  // a^c equals c^a.
  check_symmetry_ac_ca_equal: assert property (
    @(posedge clk) out[22] == out[14]
  );
  // a^d equals d^a.
  check_symmetry_ad_da_equal: assert property (
    @(posedge clk) out[21] == out[9]
  );
  // a^e equals e^a.
  check_symmetry_ae_ea_equal: assert property (
    @(posedge clk) out[20] == out[4]
  );
  // b^c equals c^b.
  check_symmetry_bc_cb_equal: assert property (
    @(posedge clk) out[17] == out[13]
  );
  // b^d equals d^b.
  check_symmetry_bd_db_equal: assert property (
    @(posedge clk) out[16] == out[8]
  );
  // b^e equals e^b.
  check_symmetry_be_eb_equal: assert property (
    @(posedge clk) out[15] == out[3]
  );
  // c^d equals d^c.
  check_symmetry_cd_dc_equal: assert property (
    @(posedge clk) out[11] == out[7]
  );
  // c^e equals e^c.
  check_symmetry_ce_ec_equal: assert property (
    @(posedge clk) out[10] == out[2]
  );
  // d^e equals e^d.
  check_symmetry_de_ed_equal: assert property (
    @(posedge clk) out[5] == out[1]
  );

endmodule