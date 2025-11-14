// SVA checker for module control
// Bind or instantiate this module and connect a property clock/reset.
module control_sva (
  input logic                 clk,
  input logic                 rst_n,
  input logic [5:0]           opcode,
  input logic [5:0]           special,
  input logic                 branch_eq,
  input logic [1:0]           if_pc_source,
  input logic                 id_rt_is_source,
  input logic                 ex_imm_command,
  input logic                 ex_alu_src_b,
  input logic                 ex_alu_rslt_src,
  input logic [1:0]           ex_dst_reg_sel,
  input logic [1:0]           ex_alu_op,
  input logic                 mem_read,
  input logic                 mem_write,
  input logic                 wb_mem_to_reg,
  input logic                 wb_reg_write
);

  // Opcodes
  localparam logic [5:0] LW    = 6'b100011;
  localparam logic [5:0] SW    = 6'b101011;
  localparam logic [5:0] BEQ   = 6'b000100;
  localparam logic [5:0] RTYPE = 6'b000000;
  localparam logic [5:0] J     = 6'b000010;
  localparam logic [5:0] JAL   = 6'b000011;
  localparam logic [5:0] ADDI  = 6'b001000;
  localparam logic [5:0] ANDI  = 6'b001100;
  localparam logic [5:0] ORI   = 6'b001101;
  localparam logic [5:0] XORI  = 6'b001110;
  localparam logic [5:0] SLTI  = 6'b001010;

  // "special" function for RTYPE
  localparam logic [5:0] JR    = 6'b001000;

  // Helpers
  logic memory_op, r_type_op, branch_op, immediate_op, jump_op, is_jr, unrec_op;

  always_comb begin
    memory_op    = (opcode == LW) || (opcode == SW);
    r_type_op    = (opcode == RTYPE);
    branch_op    = (opcode == BEQ);
    immediate_op = (opcode == ADDI) || (opcode == ANDI) || (opcode == ORI) || (opcode == XORI) || (opcode == SLTI);
    jump_op      = (opcode == J) || (opcode == JAL);
    is_jr        = (opcode == RTYPE) && (special == JR);
    unrec_op     = !(memory_op || r_type_op || immediate_op || branch_op || jump_op || is_jr);
  end

  default clocking cb @(posedge clk); endclocking
  // mask time-zero/X with reset
  // Use disable iff only where needed for conciseness
  // Basic combinational integrity
  assert property (cb ex_alu_op inside {2'b00,2'b10}) else $error("ex_alu_op illegal");
  assert property (cb ex_dst_reg_sel inside {2'b00,2'b01,2'b10}) else $error("ex_dst_reg_sel illegal");
  assert property (cb !(mem_read && mem_write)) else $error("mem_read and mem_write both 1");

  // Encoded wires must match decode
  assert property (cb id_rt_is_source == (r_type_op || branch_op || (opcode == SW)))
    else $error("id_rt_is_source decode mismatch");
  assert property (cb ex_imm_command == immediate_op)
    else $error("ex_imm_command decode mismatch");

  // Memory ops
  assert property (cb (opcode == LW) |-> (ex_alu_src_b && ex_dst_reg_sel==2'b00 && ex_alu_op==2'b00 &&
                                          wb_mem_to_reg && mem_read && !mem_write && wb_reg_write &&
                                          !ex_alu_rslt_src && if_pc_source==2'b00))
    else $error("LW controls mismatch");
  assert property (cb (opcode == SW) |-> (ex_alu_src_b && ex_dst_reg_sel==2'b00 && ex_alu_op==2'b00 &&
                                          wb_mem_to_reg && mem_write && !mem_read && !wb_reg_write &&
                                          !ex_alu_rslt_src && if_pc_source==2'b00))
    else $error("SW controls mismatch");
  assert property (cb mem_read  |-> (opcode == LW)) else $error("mem_read without LW");
  assert property (cb mem_write |-> (opcode == SW)) else $error("mem_write without SW");

  // R-type (excluding JR)
  assert property (cb (r_type_op && !is_jr) |-> (!ex_alu_src_b && ex_dst_reg_sel==2'b01 && ex_alu_op==2'b10 &&
                                                 !wb_mem_to_reg && wb_reg_write && !mem_read && !mem_write &&
                                                 !ex_alu_rslt_src && if_pc_source==2'b00))
    else $error("RTYPE controls mismatch");

  // Immediate arithmetic/logical
  assert property (cb immediate_op |-> (ex_alu_src_b && ex_dst_reg_sel==2'b00 && ex_alu_op==2'b10 &&
                                        !wb_mem_to_reg && wb_reg_write && !mem_read && !mem_write &&
                                        !ex_alu_rslt_src && if_pc_source==2'b00))
    else $error("Immediate-op controls mismatch");

  // BEQ branch
  assert property (cb (opcode == BEQ && branch_eq) |-> (if_pc_source==2'b01 &&
                                                        !ex_alu_src_b && ex_dst_reg_sel==2'b00 && ex_alu_op==2'b00 &&
                                                        !mem_read && !mem_write && !wb_mem_to_reg && !wb_reg_write &&
                                                        !ex_alu_rslt_src))
    else $error("BEQ taken controls mismatch");
  assert property (cb (opcode == BEQ && !branch_eq) |-> (if_pc_source==2'b00 &&
                                                         !ex_alu_src_b && ex_dst_reg_sel==2'b00 && ex_alu_op==2'b00 &&
                                                         !mem_read && !mem_write && !wb_mem_to_reg && !wb_reg_write &&
                                                         !ex_alu_rslt_src))
    else $error("BEQ not-taken controls mismatch");

  // Jumps
  assert property (cb (opcode == J) |-> (if_pc_source==2'b10 &&
                                         !mem_read && !mem_write && !wb_mem_to_reg && !wb_reg_write &&
                                         !ex_alu_src_b && ex_dst_reg_sel==2'b00 && ex_alu_op==2'b00 &&
                                         !ex_alu_rslt_src))
    else $error("J controls mismatch");
  assert property (cb (opcode == JAL) |-> (if_pc_source==2'b10 &&
                                           ex_dst_reg_sel==2'b10 && ex_alu_rslt_src && wb_reg_write &&
                                           !mem_read && !mem_write && !wb_mem_to_reg &&
                                           !ex_alu_src_b && ex_alu_op==2'b00))
    else $error("JAL controls mismatch");
  assert property (cb ex_alu_rslt_src |-> (opcode == JAL)) else $error("ex_alu_rslt_src asserted outside JAL");

  // JR (opcode==0 with special==JR)
  // The DUT sets if_pc_source=11 for JR; ensure no memory side-effects and rslt_src=0.
  assert property (cb is_jr |-> (if_pc_source==2'b11 &&
                                 !mem_read && !mem_write && !wb_mem_to_reg &&
                                 !ex_alu_rslt_src))
    else $error("JR controls mismatch");
  // Map if_pc_source back to decode
  assert property (cb (if_pc_source==2'b10) |-> jump_op) else $error("if_pc_source=10 without J/JAL");
  assert property (cb (if_pc_source==2'b11) |-> is_jr)   else $error("if_pc_source=11 without JR");
  assert property (cb (if_pc_source==2'b01) |-> (opcode==BEQ && branch_eq))
    else $error("if_pc_source=01 without BEQ taken");

  // Unrecognized opcode: all controls should be defaults (zeros)
  assert property (cb unrec_op |-> (if_pc_source==2'b00 && !ex_alu_src_b && !ex_alu_rslt_src &&
                                    ex_dst_reg_sel==2'b00 && ex_alu_op==2'b00 &&
                                    !mem_read && !mem_write && !wb_mem_to_reg && !wb_reg_write &&
                                    !ex_imm_command && !id_rt_is_source))
    else $error("Unrecognized opcode has non-default controls");

  // Minimal functional coverage
  cover property (cb opcode == LW);
  cover property (cb opcode == SW);
  cover property (cb r_type_op && !is_jr);
  cover property (cb is_jr);
  cover property (cb opcode == ADDI);
  cover property (cb opcode == ANDI);
  cover property (cb opcode == ORI);
  cover property (cb opcode == XORI);
  cover property (cb opcode == SLTI);
  cover property (cb opcode == BEQ && branch_eq);
  cover property (cb opcode == BEQ && !branch_eq);
  cover property (cb opcode == J);
  cover property (cb opcode == JAL);
  cover property (cb if_pc_source == 2'b00);
  cover property (cb if_pc_source == 2'b01);
  cover property (cb if_pc_source == 2'b10);
  cover property (cb if_pc_source == 2'b11);
  cover property (cb id_rt_is_source);
  cover property (cb !id_rt_is_source);
  cover property (cb ex_imm_command);
  cover property (cb !ex_imm_command);
  cover property (cb mem_read);
  cover property (cb mem_write);
  cover property (cb ex_alu_rslt_src);

endmodule

// Example bind (provide clk/rst_n from your environment):
// bind control control_sva u_control_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));