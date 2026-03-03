// SVA for memoryProtection: concise, high-quality checks + coverage
// Bind this to the DUT; no DUT edits required.

module memoryProtection_sva #(parameter int n=8, m=4);
  // Guard against under-sized parameterizations
  initial begin
    assert (n>=8 && m>=4)
      else $error("memoryProtection SVA: requires n>=8 and m>=4");
  end

  // Virtual "comb clock" on any relevant change
  event comb_ev;
  always @(addr or cs) -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  // Functional correctness (when inputs are known, outputs match spec)
  ap_func: assert property (
    !$isunknown(addr[7:0]) |-> cs[3:0] ==
      { ~addr[7],
        ~(~addr[4] & ~addr[5] & ~addr[6]),
        ~(addr[2] | addr[3]),
        ~(addr[0] & ~addr[1])
      }
  );

  // No X on outputs when inputs are known
  ap_no_x: assert property ( !$isunknown(addr[7:0]) |-> !$isunknown(cs[3:0]) );

  // Independence: each output changes only if its controlling inputs change
  ap_dep0: assert property ( $changed(cs[0]) |-> $changed(addr[1:0]) );
  ap_dep1: assert property ( $changed(cs[1]) |-> $changed(addr[3:2]) );
  ap_dep2: assert property ( $changed(cs[2]) |-> $changed(addr[6:4]) );
  ap_dep3: assert property ( $changed(cs[3]) |-> $changed(addr[7])   );

  // Functional coverage: observe both values per output (with known inputs)
  cp_cs0_hi: cover property ( !$isunknown(addr[1:0]) && cs[0]==1'b1 );
  cp_cs0_lo: cover property ( !$isunknown(addr[1:0]) && cs[0]==1'b0 );
  cp_cs1_hi: cover property ( !$isunknown(addr[3:2]) && cs[1]==1'b1 );
  cp_cs1_lo: cover property ( !$isunknown(addr[3:2]) && cs[1]==1'b0 );
  cp_cs2_hi: cover property ( !$isunknown(addr[6:4]) && cs[2]==1'b1 );
  cp_cs2_lo: cover property ( !$isunknown(addr[6:4]) && cs[2]==1'b0 );
  cp_cs3_hi: cover property ( !$isunknown(addr[7])   && cs[3]==1'b1 );
  cp_cs3_lo: cover property ( !$isunknown(addr[7])   && cs[3]==1'b0 );

  // Hit defining block conditions at least once (sanity coverage)
  cp_block1: cover property ( addr[0] && !addr[1] );
  cp_block2: cover property ( addr[2] || addr[3] );
  cp_block3: cover property ( !addr[6] && !addr[5] && !addr[4] );
  cp_block4: cover property ( addr[7] );
endmodule

bind memoryProtection memoryProtection_sva #(.n(n), .m(m)) memprot_sva_i();