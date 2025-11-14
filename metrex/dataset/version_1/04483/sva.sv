// SVA for branch_handler
`ifndef BRANCH_HANDLER_SVA
`define BRANCH_HANDLER_SVA

module branch_handler_sva
(
  input clk,
  input rst_n,

  input cmt_i_valid,
  input cmt_i_rv32,
  input cmt_i_dret,
  input cmt_i_mret,
  input cmt_i_fencei,
  input cmt_i_bjp,
  input cmt_i_bjp_prdt,
  input cmt_i_bjp_rslv,
  input [`E203_PC_SIZE-1:0] cmt_i_pc,
  input [`E203_XLEN-1:0]    cmt_i_imm,
  input [`E203_PC_SIZE-1:0] csr_epc_r,
  input [`E203_PC_SIZE-1:0] csr_dpc_r,
  input nonalu_excpirq_flush_req_raw,
  input brchmis_flush_ack,

  input cmt_i_ready,
  input brchmis_flush_req,
  input [`E203_PC_SIZE-1:0] brchmis_flush_add_op1,
  input [`E203_PC_SIZE-1:0] brchmis_flush_add_op2,
  input cmt_mret_ena,
  input cmt_dret_ena,
  input cmt_fencei_ena
);

  // Local expected behavior (from RTL intent)
  wire need_flush = ((cmt_i_bjp & (cmt_i_bjp_prdt ^ cmt_i_bjp_rslv)) |
                     cmt_i_fencei | cmt_i_mret | cmt_i_dret);
  wire is_branch  = (cmt_i_bjp | cmt_i_fencei | cmt_i_mret | cmt_i_dret);

  wire req_exp = (cmt_i_valid & need_flush) & (~nonalu_excpirq_flush_req_raw);
  wire handshaked = brchmis_flush_req & brchmis_flush_ack;

  wire [`E203_PC_SIZE-1:0] exp_op1 =
      cmt_i_dret ? csr_dpc_r :
      cmt_i_mret ? csr_epc_r :
                   cmt_i_pc;

  wire [`E203_PC_SIZE-1:0] exp_op2 =
      cmt_i_dret ? {`E203_PC_SIZE{1'b0}} :
      cmt_i_mret ? {`E203_PC_SIZE{1'b0}} :
      (cmt_i_fencei | cmt_i_bjp_prdt) ? (cmt_i_rv32 ? `E203_PC_SIZE'd4 : `E203_PC_SIZE'd2) :
      cmt_i_imm[`E203_PC_SIZE-1:0];

  wire ready_exp =
      (~is_branch) |
      (((need_flush ? (brchmis_flush_ack & ~nonalu_excpirq_flush_req_raw) : 1'b1))
        & (~nonalu_excpirq_flush_req_raw));

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Equivalence checks
  assert property (brchmis_flush_req == req_exp);
  assert property (brchmis_flush_add_op1 == exp_op1);
  assert property (brchmis_flush_add_op2 == exp_op2);
  assert property (cmt_i_ready == ready_exp);

  // Enable signals and handshake
  assert property (cmt_mret_ena   == (cmt_i_mret   & handshaked));
  assert property (cmt_dret_ena   == (cmt_i_dret   & handshaked));
  assert property (cmt_fencei_ena == (cmt_i_fencei & handshaked));

  // Basic implications
  assert property (brchmis_flush_req |-> (cmt_i_valid && ~nonalu_excpirq_flush_req_raw && need_flush));
  assert property (handshaked |-> (brchmis_flush_req && brchmis_flush_ack));
  assert property (cmt_mret_ena   |-> (cmt_i_mret   && brchmis_flush_ack));
  assert property (cmt_dret_ena   |-> (cmt_i_dret   && brchmis_flush_ack));
  assert property (cmt_fencei_ena |-> (cmt_i_fencei && brchmis_flush_ack));

  // Priority/selection checks for add ops
  assert property (cmt_i_dret |-> (brchmis_flush_add_op1 == csr_dpc_r) &&
                                (brchmis_flush_add_op2 == {`E203_PC_SIZE{1'b0}}));
  assert property (!cmt_i_dret && cmt_i_mret |-> (brchmis_flush_add_op1 == csr_epc_r) &&
                                   (brchmis_flush_add_op2 == {`E203_PC_SIZE{1'b0}}));
  assert property (!cmt_i_dret && !cmt_i_mret && (cmt_i_fencei | cmt_i_bjp_prdt)
                    |-> (brchmis_flush_add_op2 == (cmt_i_rv32 ? `E203_PC_SIZE'd4 : `E203_PC_SIZE'd2)));

  // Ready corner cases
  assert property (!is_branch |-> cmt_i_ready);
  assert property (is_branch && !need_flush |-> (cmt_i_ready == ~nonalu_excpirq_flush_req_raw));
  assert property (is_branch &&  need_flush && ~nonalu_excpirq_flush_req_raw && !brchmis_flush_ack |-> !cmt_i_ready);
  assert property (is_branch &&  need_flush && ~nonalu_excpirq_flush_req_raw &&  brchmis_flush_ack |->  cmt_i_ready);
  assert property (is_branch &&  need_flush &&  nonalu_excpirq_flush_req_raw |-> !brchmis_flush_req && !cmt_i_ready);

  // Coverage
  cover property (cmt_i_valid && cmt_i_bjp &&  cmt_i_bjp_prdt && !cmt_i_bjp_rslv && brchmis_flush_req);
  cover property (cmt_i_valid && cmt_i_bjp && !cmt_i_bjp_prdt &&  cmt_i_bjp_rslv && brchmis_flush_req);
  cover property (cmt_i_valid && cmt_i_fencei && brchmis_flush_req && brchmis_flush_ack && cmt_fencei_ena);
  cover property (cmt_i_valid && cmt_i_mret   && brchmis_flush_req && brchmis_flush_ack && cmt_mret_ena);
  cover property (cmt_i_valid && cmt_i_dret   && brchmis_flush_req && brchmis_flush_ack && cmt_dret_ena);
  cover property (cmt_i_valid && !is_branch && cmt_i_ready);
  cover property (cmt_i_fencei && cmt_i_rv32  && (brchmis_flush_add_op2 == `E203_PC_SIZE'd4));
  cover property (cmt_i_fencei && !cmt_i_rv32 && (brchmis_flush_add_op2 == `E203_PC_SIZE'd2));
  cover property (!cmt_i_dret && !cmt_i_mret && !cmt_i_fencei && !cmt_i_bjp_prdt &&
                  (brchmis_flush_add_op2 == cmt_i_imm[`E203_PC_SIZE-1:0]));
  cover property (cmt_i_valid && need_flush && nonalu_excpirq_flush_req_raw && !brchmis_flush_req);

endmodule

bind branch_handler branch_handler_sva
(
  .clk(clk),
  .rst_n(rst_n),

  .cmt_i_valid(cmt_i_valid),
  .cmt_i_rv32(cmt_i_rv32),
  .cmt_i_dret(cmt_i_dret),
  .cmt_i_mret(cmt_i_mret),
  .cmt_i_fencei(cmt_i_fencei),
  .cmt_i_bjp(cmt_i_bjp),
  .cmt_i_bjp_prdt(cmt_i_bjp_prdt),
  .cmt_i_bjp_rslv(cmt_i_bjp_rslv),
  .cmt_i_pc(cmt_i_pc),
  .cmt_i_imm(cmt_i_imm),
  .csr_epc_r(csr_epc_r),
  .csr_dpc_r(csr_dpc_r),
  .nonalu_excpirq_flush_req_raw(nonalu_excpirq_flush_req_raw),
  .brchmis_flush_ack(brchmis_flush_ack),

  .cmt_i_ready(cmt_i_ready),
  .brchmis_flush_req(brchmis_flush_req),
  .brchmis_flush_add_op1(brchmis_flush_add_op1),
  .brchmis_flush_add_op2(brchmis_flush_add_op2),
  .cmt_mret_ena(cmt_mret_ena),
  .cmt_dret_ena(cmt_dret_ena),
  .cmt_fencei_ena(cmt_fencei_ena)
);

`endif