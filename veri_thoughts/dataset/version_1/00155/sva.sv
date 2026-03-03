// SVA for trigger_control. Bind this file to the DUT.
// bind trigger_control trigger_control_sva sva_inst (.*);

module trigger_control_sva (
  input  logic        clk,
  input  logic        sync,
  input  logic        reset,

  input  logic        sel_async,      input  logic        sel_sync,       input  logic        sel_single,     input  logic        sel_gen,        input  logic        sel_pg,         input  logic        sel_dir_async,  input  logic        sel_dir_sync,   input  logic        sel_dir_single, input  logic        sel_dir_gen,    input  logic        sel_dir_pg,     input  logic        sel_chain,      input  logic        sel_sync_out,   input  logic [4:0]  src_async,      input  logic [3:0]  src_async_pos,

  input  logic [4:0]  src_sync,       input  logic        src_sync_direct,

  input  logic [4:0]  src_single,     input  logic [4:0]  src_gen,        input  logic [4:0]  src_pg,         input  logic [4:0]  dst_tbm,        input  logic [3:0]  dst_tbm_pos,
	
  input  logic [4:0]  dst_sync,       input  logic        dst_sync_direct,
	
  input  logic [4:0]  dst_dir
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Expected combinational functions
  let g_async   = sel_async   ? src_async   : 5'b0;
  let g_sync    = sel_sync    ? src_sync    : 5'b0;
  let g_single  = sel_single  ? src_single  : 5'b0;
  let g_gen     = sel_gen     ? src_gen     : 5'b0;
  let g_pg      = sel_pg      ? src_pg      : 5'b0;
  let sum_exp   = g_async | g_sync | g_single | g_gen | g_pg;

  let dir_g_async  = sel_dir_async  ? src_async  : 5'b0;
  let dir_g_sync   = sel_dir_sync   ? src_sync   : 5'b0;
  let dir_g_single = sel_dir_single ? src_single : 5'b0;
  let dir_g_gen    = sel_dir_gen    ? src_gen    : 5'b0;
  let dir_g_pg     = sel_dir_pg     ? src_pg     : 5'b0;
  let sum_dir_exp  = dir_g_async | dir_g_sync | dir_g_single | dir_g_gen | dir_g_pg;

  // Core functional checks
  assert property (dst_tbm == sum_exp);
  assert property (dst_sync == ({5{sel_sync_out && !sel_chain}} & sum_exp));
  assert property (dst_sync_direct == (sel_chain & src_sync_direct));
  assert property (dst_tbm_pos == (src_async_pos & {4{sel_async && src_async[1]}}));
  assert property (dst_dir == sum_dir_exp);

  // Sanity/gating checks
  assert property ((!sel_async && !sel_sync && !sel_single && !sel_gen && !sel_pg) |-> (dst_tbm == 5'b0 && dst_sync == 5'b0));
  assert property ((!sel_dir_async && !sel_dir_sync && !sel_dir_single && !sel_dir_gen && !sel_dir_pg) |-> (dst_dir == 5'b0));
  assert property (!sel_chain |-> (dst_sync_direct == 1'b0));

  // Knownness: known inputs imply known outputs
  assert property (
    !$isunknown({
      sel_async, sel_sync, sel_single, sel_gen, sel_pg,
      sel_dir_async, sel_dir_sync, sel_dir_single, sel_dir_gen, sel_dir_pg,
      sel_chain, sel_sync_out,
      src_async, src_sync, src_single, src_gen, src_pg,
      src_async_pos, src_sync_direct
    }) |-> !$isunknown({dst_tbm, dst_sync, dst_sync_direct, dst_tbm_pos, dst_dir})
  );

  // Coverage: exercise each path and key modes
  cover property (sel_async  && (src_async  != 5'b0));
  cover property (sel_sync   && (src_sync   != 5'b0));
  cover property (sel_single && (src_single != 5'b0));
  cover property (sel_gen    && (src_gen    != 5'b0));
  cover property (sel_pg     && (src_pg     != 5'b0));

  cover property (sel_dir_async  && (src_async  != 5'b0));
  cover property (sel_dir_sync   && (src_sync   != 5'b0));
  cover property (sel_dir_single && (src_single != 5'b0));
  cover property (sel_dir_gen    && (src_gen    != 5'b0));
  cover property (sel_dir_pg     && (src_pg     != 5'b0));

  cover property ((sel_sync_out && !sel_chain) && (sum_exp != 5'b0) && (dst_sync != 5'b0));
  cover property ((!sel_sync_out || sel_chain) && (sum_exp != 5'b0) && (dst_sync == 5'b0));

  cover property (sel_chain && src_sync_direct && dst_sync_direct);
  cover property (!sel_chain && src_sync_direct && !dst_sync_direct);

  cover property (sel_async && src_async[1] && (src_async_pos != 4'b0) && (dst_tbm_pos != 4'b0));
  cover property ((!(sel_async && src_async[1])) && (src_async_pos != 4'b0) && (dst_tbm_pos == 4'b0));

  cover property ((sel_async && sel_sync) && (src_async != 5'b0) && (src_sync != 5'b0)
                  && ((dst_tbm & src_async) != 5'b0) && ((dst_tbm & src_sync) != 5'b0));

  cover property ((sel_dir_async && sel_dir_sync) && (src_async != 5'b0) && (src_sync != 5'b0)
                  && ((dst_dir & src_async) != 5'b0) && ((dst_dir & src_sync) != 5'b0));

endmodule