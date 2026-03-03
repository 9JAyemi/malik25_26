// SVA for ex_mem pipeline register
// Concise, high-quality checks and useful coverage.
// Bind example (in your testbench or a package):
//   bind ex_mem ex_mem_sva u_ex_mem_sva (.*);

module ex_mem_sva (
  input  logic        clk,

  // IDEX side
  input  logic        s7_idex,
  input  logic        dmem_wen_idex,
  input  logic        rf_wen_idex,
  input  logic        branch2_idex,
  input  logic        mem2reg_idex,
  input  logic [15:0] aluout,
  input  logic [2:0]  flag,
  input  logic [15:0] extended_16_idex,
  input  logic [15:0] rdata2_idex,
  input  logic [3:0]  rf_waddr,
  input  logic        nop_lw_idex, nop_sw_idex,
  input  logic [15:0] branch_target_final_muxout,
  input  logic [15:0] pc_added_idex,
  input  logic        jal_idex,

  // EXMEM side
  input  logic        dmem_wen_exmem,
  input  logic        rf_wen_exmem,
  input  logic        branch2_exmem,
  input  logic        mem2reg_exmem,
  input  logic [15:0] aluout_exmem,
  input  logic [2:0]  flag_exmem,
  input  logic [15:0] rdata2_exmem,
  input  logic [3:0]  rf_waddr_exmem,
  input  logic        s7_exmem,
  input  logic [15:0] extended_exmem,
  input  logic [15:0] branch_target_exmem,
  input  logic        nop_lw_exmem, nop_sw_exmem,
  input  logic [15:0] pc_added_exmem,
  input  logic        jal_exmem
);

  // Startup guard (no explicit reset in DUT)
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking @(posedge clk); endclocking

  // One-cycle pipeline-pass assertion (all signals)
  property p_exmem_is_past_idex;
    disable iff (!past_valid)
      {
        dmem_wen_exmem, rf_wen_exmem, branch2_exmem, mem2reg_exmem,
        aluout_exmem, flag_exmem, rdata2_exmem, rf_waddr_exmem,
        s7_exmem, extended_exmem, branch_target_exmem, nop_lw_exmem, nop_sw_exmem,
        pc_added_exmem, jal_exmem
      } ==
      $past({
        dmem_wen_idex, rf_wen_idex, branch2_idex, mem2reg_idex,
        aluout,        flag,        rdata2_idex,  rf_waddr,
        s7_idex,       extended_16_idex, branch_target_final_muxout, nop_lw_idex, nop_sw_idex,
        pc_added_idex, jal_idex
      });
  endproperty
  assert property (p_exmem_is_past_idex)
    else $error("EX/MEM pipe register did not pass-through previous IDEX values");

  // No spurious output changes (any EXMEM change must be caused by an IDEX change in the prior cycle)
  property p_change_caused_by_input;
    disable iff (!past_valid)
      $changed({
        dmem_wen_exmem, rf_wen_exmem, branch2_exmem, mem2reg_exmem,
        aluout_exmem, flag_exmem, rdata2_exmem, rf_waddr_exmem,
        s7_exmem, extended_exmem, branch_target_exmem, nop_lw_exmem, nop_sw_exmem,
        pc_added_exmem, jal_exmem
      }) |-> $changed($past({
        dmem_wen_idex, rf_wen_idex, branch2_idex, mem2reg_idex,
        aluout, flag, rdata2_idex, rf_waddr,
        s7_idex, extended_16_idex, branch_target_final_muxout, nop_lw_idex, nop_sw_idex,
        pc_added_idex, jal_idex
      }));
  endproperty
  assert property (p_change_caused_by_input)
    else $error("EX/MEM outputs changed without prior IDEX change");

  // No X/Z on outputs after first cycle
  assert property (disable iff(!past_valid) !$isunknown({
    dmem_wen_exmem, rf_wen_exmem, branch2_exmem, mem2reg_exmem,
    aluout_exmem, flag_exmem, rdata2_exmem, rf_waddr_exmem,
    s7_exmem, extended_exmem, branch_target_exmem, nop_lw_exmem, nop_sw_exmem,
    pc_added_exmem, jal_exmem
  })) else $error("EX/MEM outputs contain X/Z");

  // --------------------------------
  // Coverage (concise but meaningful)
  // --------------------------------

  // Control toggles observed at EXMEM
  cover property (disable iff(!past_valid) $rose(dmem_wen_exmem));
  cover property (disable iff(!past_valid) $fell(dmem_wen_exmem));
  cover property (disable iff(!past_valid) $rose(rf_wen_exmem));
  cover property (disable iff(!past_valid) $fell(rf_wen_exmem));
  cover property (disable iff(!past_valid) $rose(branch2_exmem));
  cover property (disable iff(!past_valid) $fell(branch2_exmem));
  cover property (disable iff(!past_valid) $rose(mem2reg_exmem));
  cover property (disable iff(!past_valid) $fell(mem2reg_exmem));
  cover property (disable iff(!past_valid) $rose(s7_exmem));
  cover property (disable iff(!past_valid) $fell(s7_exmem));
  cover property (disable iff(!past_valid) $rose(nop_lw_exmem));
  cover property (disable iff(!past_valid) $fell(nop_lw_exmem));
  cover property (disable iff(!past_valid) $rose(nop_sw_exmem));
  cover property (disable iff(!past_valid) $fell(nop_sw_exmem));
  cover property (disable iff(!past_valid) $rose(jal_exmem));
  cover property (disable iff(!past_valid) $fell(jal_exmem));

  // Data-path value propagation/change
  cover property (disable iff(!past_valid) $changed(aluout_exmem));
  cover property (disable iff(!past_valid) $changed(rdata2_exmem));
  cover property (disable iff(!past_valid) $changed(extended_exmem));
  cover property (disable iff(!past_valid) $changed(branch_target_exmem));
  cover property (disable iff(!past_valid) $changed(pc_added_exmem));

  // Flags exercise (any change; and each bit seen high)
  cover property (disable iff(!past_valid) $changed(flag_exmem));
  cover property (disable iff(!past_valid) flag_exmem[0]);
  cover property (disable iff(!past_valid) flag_exmem[1]);
  cover property (disable iff(!past_valid) flag_exmem[2]);

endmodule