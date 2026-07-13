module branch_control_sva
#(
   parameter DATA_WIDTH = 32,
   parameter PC_WIDTH = 6,
   parameter PC_OFFSET_WIDTH = 25
)
(
   input logic jmp_inst_in,
   input logic jmp_use_r_in,
   input logic branch_use_r_in,
   input logic branch_inst_in,
   input logic branch_result_in,
   input logic [PC_WIDTH-1:0] pc_in,
   input logic [DATA_WIDTH-1:0] reg_a_data_in,
   input logic [DATA_WIDTH-1:0] reg_b_data_in,
   input logic [PC_OFFSET_WIDTH-1:0] pc_offset_in,
   input logic select_new_pc_out,
   input logic [PC_WIDTH-1:0] pc_out
);

   wire [DATA_WIDTH-1:0] jmp_val;
   wire [DATA_WIDTH-1:0] branch_val;
   wire [PC_WIDTH-1:0] pc_jump;

   assign pc_jump = {pc_offset_in,{2{1'b0}}};
   assign branch_val = branch_use_r_in ? reg_a_data_in : pc_in + ({reg_b_data_in,{2{1'b0}}}) + 4;
   assign jmp_val = jmp_use_r_in ? reg_a_data_in : pc_jump;

   // select_new_pc_out matches jump-or-taken-branch detection.
   check_select_new_pc_equation: assert property (
      @($global_clock) select_new_pc_out == (jmp_inst_in | (branch_inst_in & branch_result_in))
   );

   // pc_out follows the jump/branch mux implemented in the RTL.
   check_pc_out_mux_equation: assert property (
      @($global_clock) pc_out == (jmp_inst_in ? jmp_val[PC_WIDTH-1:0] : branch_val[PC_WIDTH-1:0])
   );

   // A jump target wins even when a branch is also taken.
   check_jump_priority_over_taken_branch: assert property (
      @($global_clock) (jmp_inst_in && branch_inst_in && branch_result_in) |-> (pc_out == jmp_val[PC_WIDTH-1:0])
   );

   // Jump register mode uses reg_a_data_in as the target.
   check_jump_register_target: assert property (
      @($global_clock) (jmp_inst_in && jmp_use_r_in) |-> (pc_out == reg_a_data_in[PC_WIDTH-1:0])
   );

   // Jump immediate mode uses the shifted pc_offset_in target.
   check_jump_immediate_target: assert property (
      @($global_clock) (jmp_inst_in && !jmp_use_r_in) |-> (pc_out == pc_jump)
   );

   // Without a jump, the register-selected path uses reg_a_data_in.
   check_branch_register_selected_target: assert property (
      @($global_clock) (!jmp_inst_in && branch_use_r_in) |-> (pc_out == reg_a_data_in[PC_WIDTH-1:0])
   );

   // Without a jump, the PC-relative path uses the computed branch value.
   check_branch_pc_relative_target: assert property (
      @($global_clock) (!jmp_inst_in && !branch_use_r_in) |-> (pc_out == branch_val[PC_WIDTH-1:0])
   );

endmodule