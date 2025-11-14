// SVA for mips_pipeline
// Bind with: bind mips_pipeline mips_pipeline_sva sva(.*);

module mips_pipeline_sva (
  input              clk,
  input              rst,

  input              pl_stall_mem,
  input              pl_stall_branch,
  input              pl_stall_multdiv,
  input              pl_stall_eret,
  input              exception,

  output [5:0]       ifield_fstage_opcode,
  output [4:0]       ifield_fstage_d,
  output [4:0]       ifield_fstage_t,
  output [4:0]       ifield_fstage_s,
  output [4:0]       ifield_fstage_shift,
  output [5:0]       ifield_fstage_func,

  input              pmem_cmdok,
  input  [31:0]      pmem_cmd,
  input              pmem_branch_ended,

  input              alu_multdiv_ready,

  output             pl_cause_bd,
  output             pl_pcpause,

  // internal regs from DUT (combinational "next" and registered "_d")
  input  [31:0]      pl_instr_fstage,
  input  [31:0]      pl_instr_fstage_d,
  input  [1:0]       cpu_state,
  input  [1:0]       cpu_state_d,
  input              pl_pcpause_d,
  input              instr_next,
  input              instr_next_d,
  input              pl_branch_excpt,
  input              pl_branch_excpt_d,
  input              branch_stall_was,
  input              branch_stall_was_d
);

  // mirror DUT encodings
  localparam  NORMAL        = 2'b00;
  localparam  STALL_BRANCH  = 2'b01;
  localparam  STALL_MEM     = 2'b10;
  localparam  STALL_MULTDIV = 2'b11;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior (one cycle after rst asserted)
  assert property (@(posedge clk) rst |=> (instr_next_d==0 && pl_pcpause_d==0 &&
                                           pl_branch_excpt_d==0 && branch_stall_was_d==0 &&
                                           pl_instr_fstage_d==32'd0 && cpu_state_d==NORMAL));

  // D flops capture their next values
  assert property (instr_next_d      == $past(instr_next));
  assert property (pl_pcpause_d      == $past(pl_pcpause));
  assert property (pl_branch_excpt_d == $past(pl_branch_excpt));
  assert property (branch_stall_was_d== $past(branch_stall_was));
  assert property (pl_instr_fstage_d == $past(pl_instr_fstage));
  assert property (cpu_state_d       == $past(cpu_state));

  // Decode fields reflect pl_instr_fstage_d
  assert property (ifield_fstage_opcode == pl_instr_fstage_d[31:26]);
  assert property (ifield_fstage_s      == pl_instr_fstage_d[25:21]);
  assert property (ifield_fstage_t      == pl_instr_fstage_d[20:16]);
  assert property (ifield_fstage_d      == pl_instr_fstage_d[15:11]);
  assert property (ifield_fstage_shift  == pl_instr_fstage_d[10:6]);
  assert property (ifield_fstage_func   == pl_instr_fstage_d[5:0]);

  // When PC pause is asserted, instruction word is held
  assert property (pl_pcpause |=> pl_instr_fstage_d == $past(pl_instr_fstage_d));

  // NORMAL: zero inject when pmem_cmd not ok (and no higher-priority conditions)
  assert property ((cpu_state_d==NORMAL) &&
                   !(exception || ((pl_stall_eret||pl_stall_branch)&&!pl_stall_mem)) &&
                   !(pl_stall_mem || pl_stall_multdiv) && !pmem_cmdok
                   |-> pl_instr_fstage==32'd0);

  // NORMAL: pass-through when pmem_cmd ok (and no stalls/exc)
  assert property ((cpu_state_d==NORMAL) &&
                   !(exception || ((pl_stall_eret||pl_stall_branch)&&!pl_stall_mem)) &&
                   !(pl_stall_mem || pl_stall_multdiv) && pmem_cmdok
                   |-> (pl_instr_fstage==pmem_cmd && pl_pcpause==0 && branch_stall_was==0));

  // Enter STALL_MEM or STALL_MULTDIV from NORMAL implies next state accordingly
  assert property ((cpu_state_d==NORMAL) &&
                   !(exception || ((pl_stall_eret||pl_stall_branch)&&!pl_stall_mem)) &&
                   (pl_stall_mem || pl_stall_multdiv)
                   |=> cpu_state_d == (pl_stall_mem ? STALL_MEM : STALL_MULTDIV));

  // STALL_MEM: release (no stalls/exc) => pcpause deassert, fetch from pmem_cmdok
  assert property ((cpu_state_d==STALL_MEM) &&
                   !(exception || ((pl_stall_eret||pl_stall_branch)&&!pl_stall_mem)) &&
                   !(pl_stall_mem || pl_stall_multdiv)
                   |-> (pl_pcpause==0 &&
                        pl_instr_fstage==(pmem_cmdok ? pmem_cmd : 32'd0)));

  // STALL_MULTDIV: hold while not ready
  assert property ((cpu_state_d==STALL_MULTDIV) && !exception && !alu_multdiv_ready
                   |-> (pl_pcpause==1 && pl_instr_fstage==pl_instr_fstage_d));

  // STALL_MULTDIV: ready => deassert pause, fetch from pmem
  assert property ((cpu_state_d==STALL_MULTDIV) && !exception && alu_multdiv_ready
                   |-> (pl_pcpause==0 &&
                        pl_instr_fstage==(pmem_cmdok ? pmem_cmd : 32'd0)));

  // Cause BD: in STALL_BRANCH on exc/eret/branch-without-memstall
  assert property ((cpu_state_d==STALL_BRANCH) &&
                   (exception || ((pl_stall_eret||pl_stall_branch)&&!pl_stall_mem))
                   |-> (pl_cause_bd && pl_branch_excpt));

  // Cause BD: in STALL_MEM/MULTDIV on exception reflects branch_stall_was_d
  assert property ((cpu_state_d==STALL_MEM) && (exception || ((pl_stall_eret||pl_stall_branch)&&!pl_stall_mem))
                   |-> (pl_cause_bd == branch_stall_was_d));
  assert property ((cpu_state_d==STALL_MULTDIV) && exception
                   |-> (pl_cause_bd == branch_stall_was_d));

  // STALL_BRANCH: datapath/state when no exc and no mem/div stalls
  assert property ((cpu_state_d==STALL_BRANCH) &&
                   !(exception || ((pl_stall_eret||pl_stall_branch)&&!pl_stall_mem)) &&
                   !(pl_stall_mem || pl_stall_multdiv)
                   |-> (pl_instr_fstage ==
                        (((instr_next_d || pmem_branch_ended) && pmem_cmdok && !pl_branch_excpt_d)
                          ? pmem_cmd : 32'd0)))
                   ##1 (cpu_state_d == ((pmem_branch_ended && !pl_branch_excpt_d) ? NORMAL : STALL_BRANCH));

  // STALL_BRANCH: when pmem_cmdok, clear instr_next and branch_excpt same cycle
  assert property ((cpu_state_d==STALL_BRANCH) && pmem_cmdok |-> (!instr_next && !pl_branch_excpt));

  // General safety: cause_bd only when exc or eret/branch condition holds
  assert property (pl_cause_bd |-> (exception || ((pl_stall_eret||pl_stall_branch)&&!pl_stall_mem)));

  // Coverage
  cover property (cpu_state_d==NORMAL ##1 cpu_state_d==STALL_MEM);
  cover property (cpu_state_d==NORMAL ##1 cpu_state_d==STALL_MULTDIV);
  cover property (cpu_state_d==NORMAL &&
                  (exception || ((pl_stall_eret||pl_stall_branch)&&!pl_stall_mem))
                  ##1 cpu_state_d==STALL_BRANCH);
  cover property ((cpu_state_d==STALL_BRANCH) && pmem_branch_ended && !pl_branch_excpt_d
                  ##1 cpu_state_d==NORMAL);
  cover property ((cpu_state_d==STALL_BRANCH) &&
                  (exception || ((pl_stall_eret||pl_stall_branch)&&!pl_stall_mem)) && pl_cause_bd);
  cover property ((cpu_state_d==STALL_MEM) && pl_stall_mem ##1 !(pl_stall_mem) &&
                  !(pl_stall_multdiv) && pl_pcpause==0);
  cover property ((cpu_state_d==STALL_MULTDIV) && !alu_multdiv_ready ##1 alu_multdiv_ready);
  cover property ((cpu_state_d==NORMAL) && !pmem_cmdok && pl_instr_fstage==32'd0);

endmodule

// bind example:
// bind mips_pipeline mips_pipeline_sva sva(.*);