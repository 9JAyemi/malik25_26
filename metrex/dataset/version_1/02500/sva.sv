// SVA for map_table
checker map_table_chk (
  input logic         clk, rst,
  input logic  [5:0]  p_rs, p_rt, PR_old_rd,
  input logic         p_rs_v, p_rt_v,

  input logic         hazard_stall, isDispatch,
  input logic  [4:0]  l_rs, l_rt, l_rd,
  input logic         RegDest,
  input logic  [5:0]  p_rd_new,

  input logic  [4:0]  recover_rd,
  input logic  [5:0]  p_rd_flush,
  input logic         recover,
  input logic         RegDest_ROB,

  input logic  [5:0]  p_rd_compl,
  input logic         complete,
  input logic         RegDest_compl,

  input logic         write_new_rd,              // internal wire
  input logic  [5:0]  mt [0:31],                // internal reg array
  input logic  [63:0] PR_valid                  // internal reg
);

  default clocking cb @(posedge clk); endclocking

  // Combinational relations
  assert property (p_rs     == mt[l_rs]);
  assert property (p_rt     == mt[l_rt]);
  assert property (PR_old_rd== mt[l_rd]);
  assert property (p_rs_v   == PR_valid[p_rs]);
  assert property (p_rt_v   == PR_valid[p_rt]);

  // Definition of write_new_rd must match spec
  assert property (disable iff (!rst)
                   write_new_rd == (isDispatch && RegDest && !hazard_stall && !recover));

  // Reset state
  for (genvar i=0;i<32;i++) begin
    assert property (!rst |-> (mt[i] == i[5:0]));
  end
  assert property (!rst |-> (PR_valid == 64'hFFFF_FFFF_FFFF_FFFF));
  assert property (!rst |-> (p_rs[5]==1'b0 && p_rs[4:0]==l_rs && p_rs_v));
  assert property (!rst |-> (p_rt[5]==1'b0 && p_rt[4:0]==l_rt && p_rt_v));
  assert property (!rst |-> (PR_old_rd[5]==1'b0 && PR_old_rd[4:0]==l_rd));

  // mt update semantics per index (write has priority over recover)
  for (genvar i=0;i<32;i++) begin : g_mt
    // write_new_rd updates selected entry next cycle
    assert property (disable iff (!rst)
                     $past(write_new_rd) && ($past(l_rd)==i) |-> mt[i] == $past(p_rd_new));
    // recover updates only when no write_new_rd that cycle
    assert property (disable iff (!rst)
                     !$past(write_new_rd) && $past(recover && RegDest_ROB) && ($past(recover_rd)==i)
                     |-> mt[i] == $past(p_rd_flush));
    // otherwise stable
    assert property (disable iff (!rst)
                     !$past(write_new_rd) && !$past(recover && RegDest_ROB) |-> $stable(mt[i]));
  end

  // PR_valid bit-wise next-state function with completion dominating same-cycle write
  for (genvar j=0;j<64;j++) begin : g_prv
    assert property (disable iff (!rst)
                     1 |=> PR_valid[j] ==
                           ( $past(complete && RegDest_compl && (p_rd_compl==j[5:0])) ? 1'b1 :
                             $past(write_new_rd && (p_rd_new==j[5:0]))                 ? 1'b0 :
                             $past(PR_valid[j]) ) );
  end

  // Basic X-free outputs when active
  assert property (disable iff (!rst) !$isunknown({p_rs,p_rt,PR_old_rd,p_rs_v,p_rt_v}));

  // Covers
  cover property (disable iff (!rst) write_new_rd);
  cover property (disable iff (!rst) recover && RegDest_ROB);
  cover property (disable iff (!rst) complete && RegDest_compl);
  cover property (disable iff (!rst) write_new_rd && recover && RegDest_ROB);
  cover property (disable iff (!rst) write_new_rd && complete && RegDest_compl && (p_rd_compl==p_rd_new));
  cover property (disable iff (!rst) write_new_rd && complete && RegDest_compl && (p_rd_compl!=p_rd_new));
  cover property (disable iff (!rst) write_new_rd && (l_rs==l_rd) ##1 (p_rs == $past(p_rd_new)));
  cover property (disable iff (!rst) write_new_rd && (l_rt==l_rd) ##1 (p_rt == $past(p_rd_new)));
  cover property (disable iff (!rst) recover && RegDest_ROB && (l_rs==recover_rd) ##1 (p_rs == $past(p_rd_flush)));
  cover property (disable iff (!rst) write_new_rd ##[1:$] (complete && RegDest_compl && (p_rd_compl==$past(p_rd_new))));
endchecker

bind map_table map_table_chk u_map_table_chk (
  .clk, .rst,
  .p_rs, .p_rt, .PR_old_rd,
  .p_rs_v, .p_rt_v,
  .hazard_stall, .isDispatch,
  .l_rs, .l_rt, .l_rd,
  .RegDest,
  .p_rd_new,
  .recover_rd,
  .p_rd_flush,
  .recover,
  .RegDest_ROB,
  .p_rd_compl,
  .complete,
  .RegDest_compl,
  .write_new_rd,
  .mt,
  .PR_valid
);