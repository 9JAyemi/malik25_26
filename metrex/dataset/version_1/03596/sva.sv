// SVA for trigger_output
// Bind this module to the DUT instance(s)
module trigger_output_sva (
  input  [4:0] src_async,
  input  [4:0] src_sync,
  input  [4:0] src_single,
  input  [4:0] src_gen,
  input  [4:0] src_pg,
  input        sel_async,
  input        sel_sync,
  input        sel_single,
  input        sel_gen,
  input        sel_pg,
  input        sel_chain,
  input        sel_dir_async,
  input        sel_dir_sync,
  input        sel_dir_single,
  input        sel_dir_gen,
  input        sel_dir_pg,
  input  [4:0] dst_tbm,
  input  [4:0] dst_sync,
  input  [4:0] dst_tbm_pos,
  input  [4:0] dst_sync_direct,
  input  [4:0] dst_dir
);
  default clocking cb @(*); endclocking

  // Expected combinational results
  logic [4:0] exp_sum, exp_sum_dir, exp_dst_sync, exp_dst_sync_direct, exp_tbm_pos;

  assign exp_sum = ({5{sel_async}}  & src_async) |
                   ({5{sel_sync}}   & src_sync)  |
                   ({5{sel_single}} & src_single)|
                   ({5{sel_gen}}    & src_gen)   |
                   ({5{sel_pg}}     & src_pg);

  assign exp_dst_sync_direct = ({5{sel_chain}} & src_sync);
  assign exp_dst_sync        = ({5{sel_sync}}  & ({5{!sel_chain}} & exp_sum));
  assign exp_tbm_pos         = {src_async[1], {4{sel_async & src_async[1]}}};

  assign exp_sum_dir = ({5{sel_dir_async}}  & src_async) |
                       ({5{sel_dir_sync}}   & src_sync)  |
                       ({5{sel_dir_single}} & src_single)|
                       ({5{sel_dir_gen}}    & src_gen)   |
                       ({5{sel_dir_pg}}     & src_pg);

  // X-protection predicate
  function automatic bit no_x_inputs();
    return !$isunknown({sel_async,sel_sync,sel_single,sel_gen,sel_pg,
                        sel_chain,sel_dir_async,sel_dir_sync,sel_dir_single,sel_dir_gen,sel_dir_pg,
                        src_async,src_sync,src_single,src_gen,src_pg});
  endfunction

  // Core equivalence checks
  assert property (no_x_inputs() |-> dst_tbm         == exp_sum)           else $error("dst_tbm mismatch");
  assert property (no_x_inputs() |-> dst_sync        == exp_dst_sync)      else $error("dst_sync mismatch");
  assert property (no_x_inputs() |-> dst_sync_direct == exp_dst_sync_direct) else $error("dst_sync_direct mismatch");
  assert property (no_x_inputs() |-> dst_tbm_pos     == exp_tbm_pos)       else $error("dst_tbm_pos mismatch");
  assert property (no_x_inputs() |-> dst_dir         == exp_sum_dir)       else $error("dst_dir mismatch");

  // Output must not be X when inputs are known
  assert property (no_x_inputs() |-> !$isunknown({dst_tbm,dst_sync,dst_sync_direct,dst_tbm_pos,dst_dir}))
    else $error("Outputs contain X/Z while inputs are known");

  // Chain mode exclusivity
  assert property (sel_chain  |-> dst_sync == '0);
  assert property (!sel_chain |-> dst_sync_direct == '0);

  // Sanity covers: each source alone, and chain behavior
  cover property ( sel_async  && !sel_sync && !sel_single && !sel_gen && !sel_pg &&
                   (src_async != '0) && (dst_tbm == src_async) );

  cover property (!sel_async  &&  sel_sync && !sel_single && !sel_gen && !sel_pg &&
                   (src_sync  != '0) && (dst_tbm == src_sync) );

  cover property (!sel_async  && !sel_sync &&  sel_single && !sel_gen && !sel_pg &&
                   (src_single!= '0) && (dst_tbm == src_single) );

  cover property (!sel_async  && !sel_sync && !sel_single &&  sel_gen && !sel_pg &&
                   (src_gen   != '0) && (dst_tbm == src_gen) );

  cover property (!sel_async  && !sel_sync && !sel_single && !sel_gen &&  sel_pg &&
                   (src_pg    != '0) && (dst_tbm == src_pg) );

  // Chain covers
  cover property ( sel_chain && (src_sync != '0) && (dst_sync_direct == src_sync) );
  cover property (!sel_chain && sel_sync && (exp_sum != '0) && (dst_sync == exp_sum) );

  // dst_tbm_pos special mapping covers
  cover property ( src_async[1] && !sel_async && (dst_tbm_pos == 5'b1_0000) );
  cover property ( src_async[1] &&  sel_async && (dst_tbm_pos == 5'b1_1111) );

  // Direction path cover (each dir select alone)
  cover property ( sel_dir_async  && !sel_dir_sync && !sel_dir_single && !sel_dir_gen && !sel_dir_pg &&
                   (src_async != '0) && (dst_dir == src_async) );

  cover property (!sel_dir_async  &&  sel_dir_sync && !sel_dir_single && !sel_dir_gen && !sel_dir_pg &&
                   (src_sync  != '0) && (dst_dir == src_sync) );

  cover property (!sel_dir_async  && !sel_dir_sync &&  sel_dir_single && !sel_dir_gen && !sel_dir_pg &&
                   (src_single!= '0) && (dst_dir == src_single) );

  cover property (!sel_dir_async  && !sel_dir_sync && !sel_dir_single &&  sel_dir_gen && !sel_dir_pg &&
                   (src_gen   != '0) && (dst_dir == src_gen) );

  cover property (!sel_dir_async  && !sel_dir_sync && !sel_dir_single && !sel_dir_gen &&  sel_dir_pg &&
                   (src_pg    != '0) && (dst_dir == src_pg) );

endmodule

// Example bind (bind to all trigger_output instances)
bind trigger_output trigger_output_sva sva_i (
  .src_async(src_async),
  .src_sync(src_sync),
  .src_single(src_single),
  .src_gen(src_gen),
  .src_pg(src_pg),
  .sel_async(sel_async),
  .sel_sync(sel_sync),
  .sel_single(sel_single),
  .sel_gen(sel_gen),
  .sel_pg(sel_pg),
  .sel_chain(sel_chain),
  .sel_dir_async(sel_dir_async),
  .sel_dir_sync(sel_dir_sync),
  .sel_dir_single(sel_dir_single),
  .sel_dir_gen(sel_dir_gen),
  .sel_dir_pg(sel_dir_pg),
  .dst_tbm(dst_tbm),
  .dst_sync(dst_sync),
  .dst_tbm_pos(dst_tbm_pos),
  .dst_sync_direct(dst_sync_direct),
  .dst_dir(dst_dir)
);