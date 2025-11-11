// SVA checkers and binds for half_subtractor and full_subtractor.
// Bind these in your simulation; no DUT/testbench code changes needed.

module half_subtractor_sva;
  // Bound into half_subtractor scope; can see a,b,diff,borrow

  // No X/Z on inputs/outputs
  ap_hs_no_x: assert property (@(a or b or diff or borrow)
                               !$isunknown({a,b,diff,borrow}))
    else $error("half_subtractor: X/Z detected on {a,b,diff,borrow}");

  // Functional correctness
  ap_hs_diff:   assert property (@(a or b) diff   == (a ^ b))
    else $error("half_subtractor: diff != a^b");
  ap_hs_borrow: assert property (@(a or b) borrow == ((~a) & b))
    else $error("half_subtractor: borrow != (~a)&b");

  // Input space coverage (4 combos)
  cp_hs_00: cover property (@(a or b) !a && !b);
  cp_hs_01: cover property (@(a or b) !a &&  b);
  cp_hs_10: cover property (@(a or b)  a && !b);
  cp_hs_11: cover property (@(a or b)  a &&  b);
endmodule
bind half_subtractor half_subtractor_sva hs_chk();


module full_subtractor_sva;
  // Bound into full_subtractor scope; can see a,b,c_in,diff,borrow and internals

  // No X/Z on primary I/Os
  ap_fs_no_x: assert property (@(a or b or c_in or diff or borrow)
                               !$isunknown({a,b,c_in,diff,borrow}))
    else $error("full_subtractor: X/Z detected on {a,b,c_in,diff,borrow}");

  // Functional correctness at outputs
  ap_fs_diff:   assert property (@(a or b or c_in) diff   == (a ^ b ^ c_in))
    else $error("full_subtractor: diff != a^b^c_in");
  ap_fs_borrow: assert property (@(a or b or c_in) borrow == ((~a & b) | (~(a ^ b) & c_in)))
    else $error("full_subtractor: borrow != (~a&b) | (~(a^b)&c_in)");

  // Structural/internal consistency (checks composition of two half subtractors)
  ap_fs_tdiff:   assert property (@(a or b)           temp_diff    == (a ^ b))
    else $error("full_subtractor: temp_diff != a^b");
  ap_fs_tb1:     assert property (@(a or b)           temp_borrow1 == ((~a) & b))
    else $error("full_subtractor: temp_borrow1 != (~a)&b");
  ap_fs_tb2:     assert property (@(a or b or c_in)   temp_borrow2 == ((~temp_diff) & c_in))
    else $error("full_subtractor: temp_borrow2 != (~temp_diff)&c_in");
  ap_fs_bor_or:  assert property (@(a or b or c_in)   borrow == (temp_borrow1 | temp_borrow2))
    else $error("full_subtractor: borrow != temp_borrow1|temp_borrow2");

  // At most one internal borrow active at a time
  ap_fs_onehot0: assert property (@(a or b or c_in) $onehot0({temp_borrow1,temp_borrow2}))
    else $error("full_subtractor: temp_borrow1 and temp_borrow2 cannot be 1 simultaneously");

  // Input space coverage (8 combos)
  cp_fs_000: cover property (@(a or b or c_in) {a,b,c_in} == 3'b000);
  cp_fs_001: cover property (@(a or b or c_in) {a,b,c_in} == 3'b001);
  cp_fs_010: cover property (@(a or b or c_in) {a,b,c_in} == 3'b010);
  cp_fs_011: cover property (@(a or b or c_in) {a,b,c_in} == 3'b011);
  cp_fs_100: cover property (@(a or b or c_in) {a,b,c_in} == 3'b100);
  cp_fs_101: cover property (@(a or b or c_in) {a,b,c_in} == 3'b101);
  cp_fs_110: cover property (@(a or b or c_in) {a,b,c_in} == 3'b110);
  cp_fs_111: cover property (@(a or b or c_in) {a,b,c_in} == 3'b111);

  // Ensure both internal borrow paths are exercised
  cp_fs_tb1: cover property (@(a or b)         temp_borrow1);
  cp_fs_tb2: cover property (@(a or b or c_in) temp_borrow2);
endmodule
bind full_subtractor full_subtractor_sva fs_chk();