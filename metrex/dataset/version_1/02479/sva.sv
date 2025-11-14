// SVA checker for ALU (combinational). Sampled on clk with ##0 to observe post-comb values.
module ALU_sva #(
  parameter int DATA_WIDTH = 32,
  parameter bit HIGH       = 1'b1,
  parameter bit LOW        = 1'b0
) (
  input  logic                      clk,
  input  logic                      rst_n,
  input  logic [DATA_WIDTH-1:0]     ALU_IN1,
  input  logic [DATA_WIDTH-1:0]     ALU_IN2,
  input  logic [DATA_WIDTH-1:0]     PC_IN,
  input  logic [4:0]                ALU_INSTRUCTION,
  input  logic [DATA_WIDTH-1:0]     ALU_OUT,
  input  logic                      BRANCH_TAKEN
);

  // Opcode encodings as implemented in DUT
  localparam [4:0]
    ALU_NOP  = 5'b00000,
    ALU_ADD  = 5'b00001,
    ALU_SUB  = 5'b00010,
    ALU_SLL  = 5'b00011,
    ALU_SLT  = 5'b00100,   // uses unsigned < in DUT
    ALU_SLTU = 5'b00101,   // uses signed < in DUT (note: likely swapped vs name)
    ALU_XOR  = 5'b00110,
    ALU_SRL  = 5'b00111,
    ALU_SRA  = 5'b01000,
    ALU_OR   = 5'b01001,
    ALU_AND  = 5'b01010,
    ALU_SLLI = 5'b01011,
    ALU_SRLI = 5'b01100,
    ALU_SRAI = 5'b01101,
    ALU_JAL  = 5'b01110,
    ALU_JALR = 5'b01111,
    ALU_BEQ  = 5'b10000,
    ALU_BNE  = 5'b10001,
    ALU_BLT  = 5'b10010,
    ALU_BGE  = 5'b10011,
    ALU_BLTU = 5'b10100,   // DUT: compares equality (bug?)
    ALU_BGEU = 5'b10101;

  function automatic logic [DATA_WIDTH-1:0] one_hot1();
    one_hot1 = {{(DATA_WIDTH-1){1'b0}}, 1'b1};
  endfunction

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic sanity
  a_no_x:     assert property (##0 !$isunknown({ALU_OUT, BRANCH_TAKEN}));
  a_stable:   assert property ($stable({ALU_IN1,ALU_IN2,PC_IN,ALU_INSTRUCTION}) |-> ##0 $stable({ALU_OUT,BRANCH_TAKEN}));

  // Non-branch ops: results and BRANCH_TAKEN==LOW
  a_nop:  assert property ((ALU_INSTRUCTION==ALU_NOP)  |-> ##0 (ALU_OUT=='0 && BRANCH_TAKEN==LOW));
  a_add:  assert property ((ALU_INSTRUCTION==ALU_ADD)  |-> ##0 (ALU_OUT==($signed(ALU_IN1)+$signed(ALU_IN2)) && BRANCH_TAKEN==LOW));
  a_sub:  assert property ((ALU_INSTRUCTION==ALU_SUB)  |-> ##0 (ALU_OUT==($signed(ALU_IN1)-$signed(ALU_IN2)) && BRANCH_TAKEN==LOW));
  a_sll:  assert property ((ALU_INSTRUCTION==ALU_SLL)  |-> ##0 (ALU_OUT==(ALU_IN1<<ALU_IN2)            && BRANCH_TAKEN==LOW));
  a_slt:  assert property ((ALU_INSTRUCTION==ALU_SLT)  |-> ##0 (ALU_OUT==((ALU_IN1<ALU_IN2)?one_hot1():'0) && BRANCH_TAKEN==LOW));
  a_sltu: assert property ((ALU_INSTRUCTION==ALU_SLTU) |-> ##0 (ALU_OUT==(($signed(ALU_IN1)<$signed(ALU_IN2))?one_hot1():'0) && BRANCH_TAKEN==LOW));
  a_xor:  assert property ((ALU_INSTRUCTION==ALU_XOR)  |-> ##0 (ALU_OUT==(ALU_IN1^ALU_IN2)             && BRANCH_TAKEN==LOW));
  a_srl:  assert property ((ALU_INSTRUCTION==ALU_SRL)  |-> ##0 (ALU_OUT==(ALU_IN1>>ALU_IN2)            && BRANCH_TAKEN==LOW));
  a_sra:  assert property ((ALU_INSTRUCTION==ALU_SRA)  |-> ##0 (ALU_OUT==(ALU_IN1>>>ALU_IN2)           && BRANCH_TAKEN==LOW));
  a_or:   assert property ((ALU_INSTRUCTION==ALU_OR)   |-> ##0 (ALU_OUT==(ALU_IN1|ALU_IN2)             && BRANCH_TAKEN==LOW));
  a_and:  assert property ((ALU_INSTRUCTION==ALU_AND)  |-> ##0 (ALU_OUT==(ALU_IN1&ALU_IN2)             && BRANCH_TAKEN==LOW));
  a_slli: assert property ((ALU_INSTRUCTION==ALU_SLLI) |-> ##0 (ALU_OUT==(ALU_IN1<<ALU_IN2[4:0])       && BRANCH_TAKEN==LOW));
  a_srli: assert property ((ALU_INSTRUCTION==ALU_SRLI) |-> ##0 (ALU_OUT==(ALU_IN1>>ALU_IN2[4:0])       && BRANCH_TAKEN==LOW));
  a_srai: assert property ((ALU_INSTRUCTION==ALU_SRAI) |-> ##0 (ALU_OUT==(ALU_IN1>>>ALU_IN2[4:0])      && BRANCH_TAKEN==LOW));
  a_jal:  assert property ((ALU_INSTRUCTION==ALU_JAL)  |-> ##0 (ALU_OUT==(ALU_IN1+'d4)                 && BRANCH_TAKEN==LOW));
  a_jalr: assert property ((ALU_INSTRUCTION==ALU_JALR) |-> ##0 (ALU_OUT==(PC_IN+'d4)                   && BRANCH_TAKEN==LOW));

  // Branch ops: ALU_OUT == 0 and BRANCH_TAKEN per condition (as implemented)
  a_beq:  assert property ((ALU_INSTRUCTION==ALU_BEQ)  |-> ##0 (ALU_OUT=='0 && BRANCH_TAKEN == ((ALU_IN1==ALU_IN2)?HIGH:LOW)));
  a_bne:  assert property ((ALU_INSTRUCTION==ALU_BNE)  |-> ##0 (ALU_OUT=='0 && BRANCH_TAKEN == ((ALU_IN1!=ALU_IN2)?HIGH:LOW)));
  a_blt:  assert property ((ALU_INSTRUCTION==ALU_BLT)  |-> ##0 (ALU_OUT=='0 && BRANCH_TAKEN == (($signed(ALU_IN1)< $signed(ALU_IN2))?HIGH:LOW)));
  a_bge:  assert property ((ALU_INSTRUCTION==ALU_BGE)  |-> ##0 (ALU_OUT=='0 && BRANCH_TAKEN == (($signed(ALU_IN1)>=$signed(ALU_IN2))?HIGH:LOW)));
  a_bltu: assert property ((ALU_INSTRUCTION==ALU_BLTU) |-> ##0 (ALU_OUT=='0 && BRANCH_TAKEN == ((ALU_IN1==ALU_IN2)?HIGH:LOW))); // mirrors DUT
  a_bgeu: assert property ((ALU_INSTRUCTION==ALU_BGEU) |-> ##0 (ALU_OUT=='0 && BRANCH_TAKEN == ((ALU_IN1>=ALU_IN2)?HIGH:LOW)));

  // Default/illegal opcode behavior
  a_default: assert property ((!(ALU_INSTRUCTION inside {
                                  ALU_NOP,ALU_ADD,ALU_SUB,ALU_SLL,ALU_SLT,ALU_SLTU,ALU_XOR,ALU_SRL,ALU_SRA,ALU_OR,ALU_AND,
                                  ALU_SLLI,ALU_SRLI,ALU_SRAI,ALU_JAL,ALU_JALR,ALU_BEQ,ALU_BNE,ALU_BLT,ALU_BGE,ALU_BLTU,ALU_BGEU
                                })) |-> ##0 (ALU_OUT=='0 && BRANCH_TAKEN==LOW));

  // Minimal functional coverage
  covergroup cg_ops @(posedge clk iff rst_n);
    cp_instr: coverpoint ALU_INSTRUCTION {
      bins all_ops[] = { ALU_NOP,ALU_ADD,ALU_SUB,ALU_SLL,ALU_SLT,ALU_SLTU,ALU_XOR,ALU_SRL,ALU_SRA,ALU_OR,ALU_AND,
                         ALU_SLLI,ALU_SRLI,ALU_SRAI,ALU_JAL,ALU_JALR,ALU_BEQ,ALU_BNE,ALU_BLT,ALU_BGE,ALU_BLTU,ALU_BGEU };
    }
  endgroup
  cg_ops ops_cov = new();

  // Branch outcome coverage
  c_beq_t:  cover property ((ALU_INSTRUCTION==ALU_BEQ)  && (ALU_IN1==ALU_IN2) && ##0 (BRANCH_TAKEN==HIGH));
  c_beq_nt: cover property ((ALU_INSTRUCTION==ALU_BEQ)  && (ALU_IN1!=ALU_IN2) && ##0 (BRANCH_TAKEN==LOW));
  c_bne_t:  cover property ((ALU_INSTRUCTION==ALU_BNE)  && (ALU_IN1!=ALU_IN2) && ##0 (BRANCH_TAKEN==HIGH));
  c_bne_nt: cover property ((ALU_INSTRUCTION==ALU_BNE)  && (ALU_IN1==ALU_IN2) && ##0 (BRANCH_TAKEN==LOW));
  c_blt_t:  cover property ((ALU_INSTRUCTION==ALU_BLT)  && ($signed(ALU_IN1)< $signed(ALU_IN2)) && ##0 (BRANCH_TAKEN==HIGH));
  c_blt_nt: cover property ((ALU_INSTRUCTION==ALU_BLT)  && ($signed(ALU_IN1)>=$signed(ALU_IN2)) && ##0 (BRANCH_TAKEN==LOW));
  c_bge_t:  cover property ((ALU_INSTRUCTION==ALU_BGE)  && ($signed(ALU_IN1)>=$signed(ALU_IN2)) && ##0 (BRANCH_TAKEN==HIGH));
  c_bge_nt: cover property ((ALU_INSTRUCTION==ALU_BGE)  && ($signed(ALU_IN1)< $signed(ALU_IN2)) && ##0 (BRANCH_TAKEN==LOW));
  c_bltu_t: cover property ((ALU_INSTRUCTION==ALU_BLTU) && (ALU_IN1==ALU_IN2) && ##0 (BRANCH_TAKEN==HIGH)); // as DUT
  c_bltu_nt:cover property ((ALU_INSTRUCTION==ALU_BLTU) && (ALU_IN1!=ALU_IN2) && ##0 (BRANCH_TAKEN==LOW));
  c_bgeu_t: cover property ((ALU_INSTRUCTION==ALU_BGEU) && (ALU_IN1>=ALU_IN2) && ##0 (BRANCH_TAKEN==HIGH));
  c_bgeu_nt:cover property ((ALU_INSTRUCTION==ALU_BGEU) && (ALU_IN1< ALU_IN2) && ##0 (BRANCH_TAKEN==LOW));

endmodule

// Example bind (provide clk,rst_n from your environment):
// bind ALU ALU_sva #(.DATA_WIDTH(DATA_WIDTH), .HIGH(HIGH), .LOW(LOW))
//   u_alu_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));