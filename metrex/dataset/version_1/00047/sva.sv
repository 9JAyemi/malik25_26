// SVA for INBUF_LVDS_MCCC
module INBUF_LVDS_MCCC_sva #(parameter bit STRICT_DIFF = 0) (
  input logic PADP,
  input logic PADN,
  input logic Y
);
  default clocking cb @(PADP or PADN or Y); endclocking

  // Functional equivalence (avoid race with ##0)
  a_xor_func:        assert property (1'b1 |-> ##0 (Y === (PADP ^ PADN))) else $error("Y != PADP^PADN");

  // 2-state mapping (when inputs are known 0/1)
  a_uneq_2state:     assert property (( !$isunknown({PADP,PADN}) && (PADP != PADN)) |-> ##0 (Y == 1'b1));
  a_eq_2state:       assert property (( !$isunknown({PADP,PADN}) && (PADP == PADN)) |-> ##0 (Y == 1'b0));

  // X/Z propagation
  a_xprop:           assert property ( $isunknown({PADP,PADN}) |-> ##0 $isunknown(Y));

  // No spurious Y toggle without input change
  a_no_spurious_y:   assert property ( $changed(Y) |-> ($changed(PADP) || $changed(PADN)));

  // Optional strict LVDS legality (warn when both lines equal in 2-state)
  a_strict_diff:     assert property ( STRICT_DIFF |-> ( $isunknown({PADP,PADN}) || (PADP != PADN) ))
                     else $warning("LVDS illegal common-mode state (PADP==PADN)");

  // Coverage
  c_valid_p_high:    cover property ( (PADP===1'b1 && PADN===1'b0) ##0 (Y===1'b1));
  c_valid_n_high:    cover property ( (PADP===1'b0 && PADN===1'b1) ##0 (Y===1'b1));
  c_illegal_both0:   cover property ( (PADP===1'b0 && PADN===1'b0) ##0 (Y===1'b0));
  c_illegal_both1:   cover property ( (PADP===1'b1 && PADN===1'b1) ##0 (Y===1'b0));
  c_toggle_valid:    cover property ( (PADP===1'b1 && PADN===1'b0) ##1 (PADP===1'b0 && PADN===1'b1));
  c_toggle_valid_b:  cover property ( (PADP===1'b0 && PADN===1'b1) ##1 (PADP===1'b1 && PADN===1'b0));
endmodule

bind INBUF_LVDS_MCCC INBUF_LVDS_MCCC_sva sva_inbuf_lvds_mccc (.*);