// SVA for ex_pipe_reg
// Bind with: bind ex_pipe_reg ex_pipe_reg_sva u_ex_pipe_reg_sva (.*);

module ex_pipe_reg_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        clr,

  input  logic        valid_ex_pipe_reg_i,
  input  logic [2:0]  funct3_ex_pipe_reg_i,
  input  logic [6:0]  op_ex_pipe_reg_i,
  input  logic [4:0]  rs1_ex_pipe_reg_i,
  input  logic [4:0]  rs2_ex_pipe_reg_i,
  input  logic [4:0]  rd_ex_pipe_reg_i,
  input  logic        is_r_type_ex_pipe_reg_i,
  input  logic        is_i_type_ex_pipe_reg_i,
  input  logic        is_s_type_ex_pipe_reg_i,
  input  logic        is_b_type_ex_pipe_reg_i,
  input  logic        is_u_type_ex_pipe_reg_i,
  input  logic        is_j_type_ex_pipe_reg_i,
  input  logic [1:0]  pc_sel_ex_pipe_reg_i,
  input  logic        op1sel_ex_pipe_reg_i,
  input  logic [1:0]  op2sel_ex_pipe_reg_i,
  input  logic [1:0]  wb_sel_ex_pipe_reg_i,
  input  logic        pc4_sel_ex_pipe_reg_i,
  input  logic        mem_wr_ex_pipe_reg_i,
  input  logic        cpr_en_ex_pipe_reg_i,
  input  logic        wa_sel_ex_pipe_reg_i,
  input  logic        rf_en_ex_pipe_reg_i,
  input  logic [5:0]  alu_fun_ex_pipe_reg_i,
  input  logic [31:0] next_seq_pc_ex_pipe_reg_i,
  input  logic [31:0] curr_pc_ex_pipe_reg_i,
  input  logic [31:0] next_brn_pc_ex_pipe_reg_i,
  input  logic [31:0] next_pred_pc_ex_pipe_reg_i,
  input  logic [31:0] sext_imm_ex_pipe_reg_i,
  input  logic [31:0] r_data_p1_ex_pipe_reg_i,
  input  logic [31:0] r_data_p2_ex_pipe_reg_i,
  input  logic        jump_ex_pipe_reg_i,
  input  logic        brn_pred_ex_pipe_reg_i,

  input  logic        valid_ex_pipe_reg_o,
  input  logic [2:0]  funct3_ex_pipe_reg_o,
  input  logic [6:0]  op_ex_pipe_reg_o,
  input  logic [4:0]  rs1_ex_pipe_reg_o,
  input  logic [4:0]  rs2_ex_pipe_reg_o,
  input  logic [4:0]  rd_ex_pipe_reg_o,
  input  logic        is_r_type_ex_pipe_reg_o,
  input  logic        is_i_type_ex_pipe_reg_o,
  input  logic        is_s_type_ex_pipe_reg_o,
  input  logic        is_b_type_ex_pipe_reg_o,
  input  logic        is_u_type_ex_pipe_reg_o,
  input  logic        is_j_type_ex_pipe_reg_o,
  input  logic [1:0]  pc_sel_ex_pipe_reg_o,
  input  logic        op1sel_ex_pipe_reg_o,
  input  logic [1:0]  op2sel_ex_pipe_reg_o,
  input  logic [1:0]  wb_sel_ex_pipe_reg_o,
  input  logic        pc4_sel_ex_pipe_reg_o,
  input  logic        mem_wr_ex_pipe_reg_o,
  input  logic        cpr_en_ex_pipe_reg_o,
  input  logic        wa_sel_ex_pipe_reg_o,
  input  logic        rf_en_ex_pipe_reg_o,
  input  logic [5:0]  alu_fun_ex_pipe_reg_o,
  input  logic [31:0] next_seq_pc_ex_pipe_reg_o,
  input  logic [31:0] curr_pc_ex_pipe_reg_o,
  input  logic [31:0] next_brn_pc_ex_pipe_reg_o,
  input  logic [31:0] next_pred_pc_ex_pipe_reg_o,
  input  logic [31:0] sext_imm_ex_pipe_reg_o,
  input  logic [31:0] r_data_p1_ex_pipe_reg_o,
  input  logic [31:0] r_data_p2_ex_pipe_reg_o,
  input  logic        jump_ex_pipe_reg_o,
  input  logic        brn_pred_ex_pipe_reg_o
);

  default clocking cb @(posedge clk); endclocking

  // Flattened buses to keep checks concise
  localparam int BUS_W_I = $bits({
    valid_ex_pipe_reg_i, funct3_ex_pipe_reg_i, op_ex_pipe_reg_i,
    rs1_ex_pipe_reg_i, rs2_ex_pipe_reg_i, rd_ex_pipe_reg_i,
    is_r_type_ex_pipe_reg_i, is_i_type_ex_pipe_reg_i, is_s_type_ex_pipe_reg_i,
    is_b_type_ex_pipe_reg_i, is_u_type_ex_pipe_reg_i, is_j_type_ex_pipe_reg_i,
    pc_sel_ex_pipe_reg_i, op1sel_ex_pipe_reg_i, op2sel_ex_pipe_reg_i,
    wb_sel_ex_pipe_reg_i, pc4_sel_ex_pipe_reg_i, mem_wr_ex_pipe_reg_i,
    cpr_en_ex_pipe_reg_i, wa_sel_ex_pipe_reg_i, rf_en_ex_pipe_reg_i,
    alu_fun_ex_pipe_reg_i,
    next_seq_pc_ex_pipe_reg_i, curr_pc_ex_pipe_reg_i,
    next_brn_pc_ex_pipe_reg_i, next_pred_pc_ex_pipe_reg_i,
    sext_imm_ex_pipe_reg_i, r_data_p1_ex_pipe_reg_i, r_data_p2_ex_pipe_reg_i,
    jump_ex_pipe_reg_i, brn_pred_ex_pipe_reg_i
  });

  localparam int BUS_W_O = $bits({
    valid_ex_pipe_reg_o, funct3_ex_pipe_reg_o, op_ex_pipe_reg_o,
    rs1_ex_pipe_reg_o, rs2_ex_pipe_reg_o, rd_ex_pipe_reg_o,
    is_r_type_ex_pipe_reg_o, is_i_type_ex_pipe_reg_o, is_s_type_ex_pipe_reg_o,
    is_b_type_ex_pipe_reg_o, is_u_type_ex_pipe_reg_o, is_j_type_ex_pipe_reg_o,
    pc_sel_ex_pipe_reg_o, op1sel_ex_pipe_reg_o, op2sel_ex_pipe_reg_o,
    wb_sel_ex_pipe_reg_o, pc4_sel_ex_pipe_reg_o, mem_wr_ex_pipe_reg_o,
    cpr_en_ex_pipe_reg_o, wa_sel_ex_pipe_reg_o, rf_en_ex_pipe_reg_o,
    alu_fun_ex_pipe_reg_o,
    next_seq_pc_ex_pipe_reg_o, curr_pc_ex_pipe_reg_o,
    next_brn_pc_ex_pipe_reg_o, next_pred_pc_ex_pipe_reg_o,
    sext_imm_ex_pipe_reg_o, r_data_p1_ex_pipe_reg_o, r_data_p2_ex_pipe_reg_o,
    jump_ex_pipe_reg_o, brn_pred_ex_pipe_reg_o
  });

  initial assert (BUS_W_I == BUS_W_O)
    else $error("ex_pipe_reg: input/output bus width mismatch");

  logic [BUS_W_I-1:0] i_bus = {
    valid_ex_pipe_reg_i, funct3_ex_pipe_reg_i, op_ex_pipe_reg_i,
    rs1_ex_pipe_reg_i, rs2_ex_pipe_reg_i, rd_ex_pipe_reg_i,
    is_r_type_ex_pipe_reg_i, is_i_type_ex_pipe_reg_i, is_s_type_ex_pipe_reg_i,
    is_b_type_ex_pipe_reg_i, is_u_type_ex_pipe_reg_i, is_j_type_ex_pipe_reg_i,
    pc_sel_ex_pipe_reg_i, op1sel_ex_pipe_reg_i, op2sel_ex_pipe_reg_i,
    wb_sel_ex_pipe_reg_i, pc4_sel_ex_pipe_reg_i, mem_wr_ex_pipe_reg_i,
    cpr_en_ex_pipe_reg_i, wa_sel_ex_pipe_reg_i, rf_en_ex_pipe_reg_i,
    alu_fun_ex_pipe_reg_i,
    next_seq_pc_ex_pipe_reg_i, curr_pc_ex_pipe_reg_i,
    next_brn_pc_ex_pipe_reg_i, next_pred_pc_ex_pipe_reg_i,
    sext_imm_ex_pipe_reg_i, r_data_p1_ex_pipe_reg_i, r_data_p2_ex_pipe_reg_i,
    jump_ex_pipe_reg_i, brn_pred_ex_pipe_reg_i
  };

  logic [BUS_W_O-1:0] o_bus = {
    valid_ex_pipe_reg_o, funct3_ex_pipe_reg_o, op_ex_pipe_reg_o,
    rs1_ex_pipe_reg_o, rs2_ex_pipe_reg_o, rd_ex_pipe_reg_o,
    is_r_type_ex_pipe_reg_o, is_i_type_ex_pipe_reg_o, is_s_type_ex_pipe_reg_o,
    is_b_type_ex_pipe_reg_o, is_u_type_ex_pipe_reg_o, is_j_type_ex_pipe_reg_o,
    pc_sel_ex_pipe_reg_o, op1sel_ex_pipe_reg_o, op2sel_ex_pipe_reg_o,
    wb_sel_ex_pipe_reg_o, pc4_sel_ex_pipe_reg_o, mem_wr_ex_pipe_reg_o,
    cpr_en_ex_pipe_reg_o, wa_sel_ex_pipe_reg_o, rf_en_ex_pipe_reg_o,
    alu_fun_ex_pipe_reg_o,
    next_seq_pc_ex_pipe_reg_o, curr_pc_ex_pipe_reg_o,
    next_brn_pc_ex_pipe_reg_o, next_pred_pc_ex_pipe_reg_o,
    sext_imm_ex_pipe_reg_o, r_data_p1_ex_pipe_reg_o, r_data_p2_ex_pipe_reg_o,
    jump_ex_pipe_reg_o, brn_pred_ex_pipe_reg_o
  };

  // Reset/clear drives zero and known
  assert property ( (reset || clr) |-> (o_bus == '0 && !$isunknown(o_bus)) );

  // Register pass-through on rising edge
  assert property (
    (!reset && !clr && !$past(reset || clr))
      |-> (o_bus == $past(i_bus))
  );

  // Known-propagation: known inputs produce known outputs next cycle
  assert property (
    (!reset && !clr && !$past(reset || clr) && !$isunknown($past(i_bus)))
      |-> !$isunknown(o_bus)
  );

  // Coverage
  cover property ($rose(reset));
  cover property ($rose(clr));
  cover property (!reset && !clr && $changed(i_bus) ##1 (o_bus == $past(i_bus)));
  cover property (!reset && !clr && $rose(valid_ex_pipe_reg_i) ##1 valid_ex_pipe_reg_o);

  // Per-control-bit propagation coverage
  localparam int CTRL_W = $bits({
    valid_ex_pipe_reg_i,
    is_r_type_ex_pipe_reg_i, is_i_type_ex_pipe_reg_i, is_s_type_ex_pipe_reg_i,
    is_b_type_ex_pipe_reg_i, is_u_type_ex_pipe_reg_i, is_j_type_ex_pipe_reg_i,
    op1sel_ex_pipe_reg_i, pc4_sel_ex_pipe_reg_i, mem_wr_ex_pipe_reg_i,
    cpr_en_ex_pipe_reg_i, wa_sel_ex_pipe_reg_i, rf_en_ex_pipe_reg_i,
    jump_ex_pipe_reg_i, brn_pred_ex_pipe_reg_i
  });

  logic [CTRL_W-1:0] ctrl_i = {
    valid_ex_pipe_reg_i,
    is_r_type_ex_pipe_reg_i, is_i_type_ex_pipe_reg_i, is_s_type_ex_pipe_reg_i,
    is_b_type_ex_pipe_reg_i, is_u_type_ex_pipe_reg_i, is_j_type_ex_pipe_reg_i,
    op1sel_ex_pipe_reg_i, pc4_sel_ex_pipe_reg_i, mem_wr_ex_pipe_reg_i,
    cpr_en_ex_pipe_reg_i, wa_sel_ex_pipe_reg_i, rf_en_ex_pipe_reg_i,
    jump_ex_pipe_reg_i, brn_pred_ex_pipe_reg_i
  };

  logic [CTRL_W-1:0] ctrl_o = {
    valid_ex_pipe_reg_o,
    is_r_type_ex_pipe_reg_o, is_i_type_ex_pipe_reg_o, is_s_type_ex_pipe_reg_o,
    is_b_type_ex_pipe_reg_o, is_u_type_ex_pipe_reg_o, is_j_type_ex_pipe_reg_o,
    op1sel_ex_pipe_reg_o, pc4_sel_ex_pipe_reg_o, mem_wr_ex_pipe_reg_o,
    cpr_en_ex_pipe_reg_o, wa_sel_ex_pipe_reg_o, rf_en_ex_pipe_reg_o,
    jump_ex_pipe_reg_o, brn_pred_ex_pipe_reg_o
  };

  genvar k;
  generate
    for (k = 0; k < CTRL_W; k++) begin : gen_cov_ctrl
      cover property (!reset && !clr && $rose(ctrl_i[k]) ##1 ctrl_o[k]);
    end
  endgenerate

endmodule

// Bind into the DUT
bind ex_pipe_reg ex_pipe_reg_sva u_ex_pipe_reg_sva (.*);