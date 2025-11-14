// SVA checker for antares_exmem_register
// Focused, high-quality assertions and coverage of reset, stall/flush gating, propagation, and movz/movn write-enable logic.

bind antares_exmem_register antares_exmem_register_sva();

module antares_exmem_register_sva;
  // Use bound instance's signals by name
  default clocking cb @(posedge clk); endclocking

  // Make $past safe from time 0
  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Convenience concatenations
  `define ALL_OUTS { \
    mem_alu_result,           /*32*/ \
    mem_mem_store_data,       /*32*/ \
    mem_gpr_wa,               /*5*/  \
    mem_gpr_we,               /*1*/  \
    mem_mem_to_gpr_select,    /*1*/  \
    mem_mem_write,            /*1*/  \
    mem_mem_byte,             /*1*/  \
    mem_mem_halfword,         /*1*/  \
    mem_mem_data_sign_ext,    /*1*/  \
    mem_exception_pc,         /*32*/ \
    mem_llsc,                 /*1*/  \
    mem_kernel_mode,          /*1*/  \
    mem_is_bds,               /*1*/  \
    mem_trap,                 /*1*/  \
    mem_trap_condition,       /*1*/  \
    mem_mem_exception_source  /*1*/  \
  }

  `define SIMPLE_OUTS { \
    mem_alu_result, mem_mem_store_data, mem_gpr_wa, \
    mem_mem_byte, mem_mem_halfword, mem_mem_data_sign_ext, \
    mem_exception_pc, mem_llsc, mem_kernel_mode, mem_is_bds, mem_trap_condition \
  }

  `define SIMPLE_EXS { \
    ex_alu_result, ex_mem_store_data, ex_gpr_wa, \
    ex_mem_byte, ex_mem_halfword, ex_mem_data_sign_ext, \
    ex_exception_pc, ex_llsc, ex_kernel_mode, ex_is_bds, ex_trap_condition \
  }

  // Reset: next cycle after rst==1, all outputs are reset to 0
  assert property (past_valid && $past(rst) |-> `ALL_OUTS == {113{1'b0}})
    else $error("Reset values mismatch");

  // Hold on mem_stall: when not in reset and mem_stall was 1, all outputs hold their previous value
  assert property (past_valid && !$past(rst) && $past(mem_stall) |-> `ALL_OUTS == $past(`ALL_OUTS))
    else $error("mem_stall hold behavior violated");

  // Simple propagation (no mem_stall, no reset)
  assert property (past_valid && !$past(rst) && !$past(mem_stall) |-> `SIMPLE_OUTS == $past(`SIMPLE_EXS))
    else $error("Simple propagation mismatch");

  // Zero on ex_stall/ex_flush for the gated controls
  assert property (past_valid && !$past(rst) && !$past(mem_stall) && $past(ex_stall || ex_flush) |->
                   {mem_gpr_we, mem_mem_to_gpr_select, mem_mem_write, mem_trap, mem_mem_exception_source} == 5'b0)
    else $error("Gated controls not cleared on ex_stall/ex_flush");

  // Propagation of gated controls when not blocked (excluding mem_gpr_we special mov logic)
  assert property (past_valid && !$past(rst) && !$past(mem_stall) && !$past(ex_stall || ex_flush) |->
                   {mem_mem_to_gpr_select, mem_mem_write, mem_trap, mem_mem_exception_source} ==
                   $past({ex_mem_to_gpr_select, ex_mem_write, ex_trap, ex_mem_exception_source}))
    else $error("Gated control propagation mismatch");

  // mem_gpr_we movz/movn conditional write-enable when not blocked
  // If movz/movn active, mem_gpr_we equals computed condition; otherwise it passes through ex_gpr_we
  assert property (past_valid && !$past(rst) && !$past(mem_stall) && !$past(ex_stall || ex_flush) &&
                   $past(ex_movz || ex_movn) |->
                   mem_gpr_we == ( ($past(ex_movn) && !$past(ex_b_is_zero)) ||
                                   ($past(ex_movz) &&  $past(ex_b_is_zero)) ))
    else $error("mem_gpr_we movz/movn conditional mismatch");

  assert property (past_valid && !$past(rst) && !$past(mem_stall) && !$past(ex_stall || ex_flush) &&
                   !$past(ex_movz || ex_movn) |->
                   mem_gpr_we == $past(ex_gpr_we))
    else $error("mem_gpr_we passthrough mismatch");

  // Coverage

  // Cover reset taking effect
  cover property (past_valid && $past(rst) && (`ALL_OUTS == {113{1'b0}}));

  // Cover mem_stall holding values
  cover property (past_valid && !$past(rst) && $past(mem_stall) && (`ALL_OUTS == $past(`ALL_OUTS)));

  // Cover flush clears gated controls
  cover property (past_valid && !$past(rst) && !$past(mem_stall) && $past(ex_flush) &&
                  {mem_gpr_we, mem_mem_to_gpr_select, mem_mem_write, mem_trap, mem_mem_exception_source} == 5'b0);

  // Cover stall clears gated controls
  cover property (past_valid && !$past(rst) && !$past(mem_stall) && $past(ex_stall) &&
                  {mem_gpr_we, mem_mem_to_gpr_select, mem_mem_write, mem_trap, mem_mem_exception_source} == 5'b0);

  // Cover movz: B==0 -> no write; B==1 -> write
  cover property (past_valid && !$past(rst) && !$past(mem_stall) && !$past(ex_stall || ex_flush) &&
                  $past(ex_movz) && !$past(ex_b_is_zero) && !mem_gpr_we);
  cover property (past_valid && !$past(rst) && !$past(mem_stall) && !$past(ex_stall || ex_flush) &&
                  $past(ex_movz) &&  $past(ex_b_is_zero) &&  mem_gpr_we);

  // Cover movn: B==0 -> write; B==1 -> no write
  cover property (past_valid && !$past(rst) && !$past(mem_stall) && !$past(ex_stall || ex_flush) &&
                  $past(ex_movn) && !$past(ex_b_is_zero) &&  mem_gpr_we);
  cover property (past_valid && !$past(rst) && !$past(mem_stall) && !$past(ex_stall || ex_flush) &&
                  $past(ex_movn) &&  $past(ex_b_is_zero) && !mem_gpr_we);

  // Cover plain propagation on at least one cycle
  cover property (past_valid && !$past(rst) && !$past(mem_stall) &&
                  (`SIMPLE_OUTS == $past(`SIMPLE_EXS)));

endmodule