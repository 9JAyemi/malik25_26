// SVA for nor2/nor3. Bind these to the DUT.
// Focus: functional correctness, no-X when inputs known, no spurious toggles, and basic coverage.

module nor2_sva (input logic a, b, out);
  // Functional equivalence (combinational, delta-cycle accurate when inputs are known)
  ap_nor2_func:
    assert property (@(a or b or out) disable iff ($isunknown({a,b}))
                     out == ~(a | b));

  // If inputs are known, output must be known
  ap_nor2_known_out:
    assert property (@(a or b or out) !$isunknown({a,b}) |-> !$isunknown(out));

  // Output changes only when some input changes
  ap_nor2_no_spurious_out:
    assert property (@(a or b or out) disable iff ($isunknown({a,b,out}))
                     $changed(out) |-> $changed({a,b}));

  // Coverage: all input combinations and both output edges
  cp_nor2_00: cover property (@(a or b) !a && !b &&  out);
  cp_nor2_01: cover property (@(a or b)  a && !b && !out);
  cp_nor2_10: cover property (@(a or b) !a &&  b && !out);
  cp_nor2_11: cover property (@(a or b)  a &&  b && !out);

  cp_nor2_out_rise: cover property (@(out) $rose(out));
  cp_nor2_out_fall: cover property (@(out) $fell(out));
endmodule

bind nor2 nor2_sva nor2_sva_i (.a(a), .b(b), .out(out));


module nor3_sva (input logic a, b, c, out,
                 input logic temp_out, u1_out);
  // Internal temp_out must be NOR(a,b) when inputs known
  ap_nor3_temp_func:
    assert property (@(a or b or temp_out) disable iff ($isunknown({a,b}))
                     temp_out == ~(a | b));

  // temp_out driven consistently by both sources (no contention/mismatch)
  ap_nor3_temp_alias:
    assert property (@(temp_out or u1_out) disable iff ($isunknown({temp_out,u1_out}))
                     temp_out == u1_out);

  // Top-level functional equivalence: out = ~(a|b) & ~c when inputs known
  ap_nor3_func:
    assert property (@(a or b or c or out) disable iff ($isunknown({a,b,c}))
                     out == (~(a | b)) & ~c);

  // If inputs known, internal and output must be known
  ap_nor3_known_temp:
    assert property (@(a or b or temp_out) !$isunknown({a,b}) |-> !$isunknown(temp_out));
  ap_nor3_known_out:
    assert property (@(a or b or c or out) !$isunknown({a,b,c}) |-> !$isunknown(out));

  // Output changes only when some input changes
  ap_nor3_no_spurious_out:
    assert property (@(a or b or c or out) disable iff ($isunknown({a,b,c,out}))
                     $changed(out) |-> $changed({a,b,c}));

  // Coverage: all input combinations (8 states) and edge activity
  cp_nor3_000: cover property (@(a or b or c) !a && !b && !c &&  out);
  cp_nor3_001: cover property (@(a or b or c) !a && !b &&  c && !out);
  cp_nor3_010: cover property (@(a or b or c) !a &&  b && !c && !out);
  cp_nor3_011: cover property (@(a or b or c) !a &&  b &&  c && !out);
  cp_nor3_100: cover property (@(a or b or c)  a && !b && !c && !out);
  cp_nor3_101: cover property (@(a or b or c)  a && !b &&  c && !out);
  cp_nor3_110: cover property (@(a or b or c)  a &&  b && !c && !out);
  cp_nor3_111: cover property (@(a or b or c)  a &&  b &&  c && !out);

  cp_nor3_temp_rise: cover property (@(temp_out) $rose(temp_out));
  cp_nor3_temp_fall: cover property (@(temp_out) $fell(temp_out));
  cp_nor3_out_rise:  cover property (@(out)      $rose(out));
  cp_nor3_out_fall:  cover property (@(out)      $fell(out));
endmodule

bind nor3 nor3_sva nor3_sva_i (.a(a), .b(b), .c(c), .out(out),
                                .temp_out(temp_out), .u1_out(u1.out));