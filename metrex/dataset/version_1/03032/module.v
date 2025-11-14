
module mips_pipeline    (
                        input             clk,
                        input             rst,

                        input             pl_stall_mem,
                        input             pl_stall_branch,
                        input             pl_stall_multdiv,
                        input             pl_stall_eret,
                        input             exception,

                        output[5:0]       ifield_fstage_opcode,
                        output[4:0]       ifield_fstage_d,
                        output[4:0]       ifield_fstage_t,
                        output[4:0]       ifield_fstage_s,
                        output[4:0]       ifield_fstage_shift,
                        output[5:0]       ifield_fstage_func,

                        input             pmem_cmdok,
                        input[31:0]       pmem_cmd,
                        input             pmem_branch_ended,

                        input             alu_multdiv_ready,

                        output reg        pl_cause_bd,
                        output reg        pl_pcpause
                        );




  reg[31:0]   pl_instr_fstage;
  reg[31:0]   pl_instr_fstage_d;
  reg[1:0]    cpu_state;
  reg[1:0]    cpu_state_d;

  reg         pl_pcpause_d;
  reg         instr_next;
  reg         instr_next_d;
  reg         pl_branch_excpt;
  reg         pl_branch_excpt_d;
  reg         branch_stall_was;
  reg         branch_stall_was_d;
  localparam  NORMAL=         2'b00,
              STALL_BRANCH=   2'b01,
              STALL_MEM=      2'b10,
              STALL_MULTDIV=  2'b11;




  assign ifield_fstage_opcode= pl_instr_fstage_d[31:26];
  assign ifield_fstage_s= pl_instr_fstage_d[25:21];
  assign ifield_fstage_t= pl_instr_fstage_d[20:16];
  assign ifield_fstage_d= pl_instr_fstage_d[15:11];
  assign ifield_fstage_shift= pl_instr_fstage_d[10:6];
  assign ifield_fstage_func= pl_instr_fstage_d[5:0];

  always @*
  begin
  pl_instr_fstage= pmem_cmd;
  cpu_state= NORMAL;
  instr_next= instr_next_d;
  pl_pcpause= pl_pcpause_d;
  branch_stall_was= branch_stall_was_d;
  pl_cause_bd= 1'b0;
  pl_branch_excpt= pl_branch_excpt_d;

  case(cpu_state_d)
  NORMAL:
    begin
    pl_pcpause= 1'b0;
    branch_stall_was= 1'b0;
    if(exception | ((pl_stall_eret | pl_stall_branch) & !pl_stall_mem))
      begin
      instr_next= !pmem_cmdok & !(pl_stall_eret | exception);
                  pl_instr_fstage= pl_stall_eret | exception | !pmem_cmdok ? 32'd0 :
                       pmem_cmd;
      cpu_state= STALL_BRANCH;
      end
    else if(pl_stall_mem | pl_stall_multdiv)
      begin
      pl_pcpause= 1'b1;
      pl_instr_fstage= pl_instr_fstage_d;
      cpu_state= pl_stall_mem ? STALL_MEM : STALL_MULTDIV;
      end
    else if(!pmem_cmdok) pl_instr_fstage= 32'd0;
    end
  STALL_BRANCH:
    begin
    branch_stall_was= 1'b1;
    if(pmem_cmdok)
      begin
      instr_next= 1'b0;
      pl_branch_excpt= 1'b0;
      end

    if(exception | ((pl_stall_eret | pl_stall_branch) & !pl_stall_mem))
      begin
      pl_instr_fstage= 32'd0;
      pl_cause_bd= 1'b1;
      pl_branch_excpt= 1'b1;
      cpu_state= STALL_BRANCH;
      end
    else if(pl_stall_mem | pl_stall_multdiv)
      begin
      pl_pcpause= 1'b1;
      pl_instr_fstage= pl_instr_fstage_d;
      cpu_state= pl_stall_mem ? STALL_MEM : STALL_MULTDIV;
      end
    else
      begin
      pl_instr_fstage= (instr_next_d | pmem_branch_ended) &
                       pmem_cmdok  & !pl_branch_excpt_d ? pmem_cmd : 32'd0;
      cpu_state= pmem_branch_ended & !pl_branch_excpt_d ? NORMAL : STALL_BRANCH;
      end
    end
  STALL_MEM:
    begin
    if(exception | ((pl_stall_eret | pl_stall_branch) & !pl_stall_mem))
      begin
      pl_pcpause= 1'b0;
      if(branch_stall_was_d) pl_cause_bd= 1'b1;
      instr_next= !pmem_cmdok & !(pl_stall_eret | exception);
                  pl_instr_fstage= pl_stall_eret | exception | !pmem_cmdok ? 32'd0 :
                       pmem_cmd;
      cpu_state= STALL_BRANCH;
      end
    else if(pl_stall_mem | pl_stall_multdiv)
      begin
      pl_pcpause= 1'b1;
      pl_instr_fstage= pl_instr_fstage_d;
      cpu_state= pl_stall_mem ? STALL_MEM : STALL_MULTDIV;
      end
    else
      begin
      pl_pcpause= 1'b0;
      pl_instr_fstage= pmem_cmdok ? pmem_cmd : 32'd0;
      end
    end
  STALL_MULTDIV:
    begin
    if(exception)
      begin
      if(branch_stall_was_d) pl_cause_bd= 1'b1;
      instr_next= !pmem_cmdok & !(pl_stall_eret | exception);
                  pl_instr_fstage= pl_stall_eret | exception | !pmem_cmdok ? 32'd0 :
                       pmem_cmd;
      cpu_state= STALL_BRANCH;
      end
    else
      begin
      if(!alu_multdiv_ready)
        begin
        pl_pcpause= 1'b1;
        pl_instr_fstage= pl_instr_fstage_d;
        cpu_state= STALL_MULTDIV;
        end
      else
        begin
        pl_pcpause= 1'b0;
        pl_instr_fstage= pmem_cmdok ? pmem_cmd : 32'd0;
        end
      end
    end
  endcase
  end

  always @(posedge clk)
  begin
  if(rst)
    begin
    instr_next_d<= 1'b0;
    pl_pcpause_d<= 1'b0;
    pl_branch_excpt_d<= 1'b0;
    branch_stall_was_d<= 1'b0;
    pl_instr_fstage_d<= 32'd0;
    cpu_state_d<= NORMAL;
    end
  else
    begin
    instr_next_d<= instr_next;
    pl_pcpause_d<= pl_pcpause;
    pl_branch_excpt_d<= pl_branch_excpt;
    branch_stall_was_d<= branch_stall_was;
    pl_instr_fstage_d<= pl_instr_fstage;
    cpu_state_d<= cpu_state;
    end
  end




endmodule
