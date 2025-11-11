// SVA for ControlUnit
// Bind this file to the DUT:
// bind ControlUnit ControlUnit_sva cu_sva_inst (.*);

module ControlUnit_sva (
  input logic              clk,
  input logic [4:0]        OPCODE,
  input logic [4:0]        BOpCode,
  input logic              Zero,
  input logic              BSelector,
  input logic              MemRD,
  input logic              MemWD,
  input logic              RegWrite,
  input logic [1:0]        RegSelector,
  input logic              PCSelect,
  input logic              Enable1,
  input logic              Enable2,
  input logic              Enable3,
  input logic              Enable4
);

  // Mirror encodings from DUT
  localparam logic [4:0]
    ADD  = 5'd0,  SUB  = 5'd1,  ADDI = 5'd2,  SUBI = 5'd3,
    MLT  = 5'd4,  MLTI = 5'd5,  AND  = 5'd6,  OR   = 5'd7,
    ANDI = 5'd8,  ORI  = 5'd9,  SLR  = 5'd10, SLL  = 5'd11,
    LDR  = 5'd12, STR  = 5'd13, BNE  = 5'd14, BEQ  = 5'd15,
    J    = 5'd16, CMP  = 5'd17, NOP  = 5'b11111;

  default clocking cb @(posedge clk); endclocking
  // Avoid spurious failures when inputs are X at sample time
  default disable iff ($isunknown({OPCODE,BOpCode,Zero}));

  // Output should never be X/Z
  a_no_x_outputs: assert property (!$isunknown({BSelector,MemRD,MemWD,RegWrite,RegSelector,PCSelect,Enable1,Enable2,Enable3,Enable4}));

  // Enables are constant 1s (DUT never changes them after init)
  a_enables_stuck1: assert property (Enable1 && Enable2 && Enable3 && Enable4);

  // Mutual exclusion of memory controls
  a_mem_mutex: assert property (!(MemRD && MemWD));

  // RegSelector never 2'b11
  a_regsel_domain: assert property (RegSelector inside {2'd0,2'd1,2'd2});

  // Check initial defaults at time 0 (per DUT initial block)
  a_init_defaults: assert property (
    $initstate |-> (BSelector==1'd0 && PCSelect==1'd0 && MemRD==1'd0 && MemWD==1'd0 &&
                    RegWrite==1'd0 && RegSelector==2'd0 && Enable1 && Enable2 && Enable3 && Enable4)
  );

  // Decode checks per OPCODE
  a_ADD :  assert property (OPCODE==ADD  |-> (BSelector==0 && MemRD==0 && MemWD==0 && RegWrite==1 && RegSelector==2'd0));
  a_SUB :  assert property (OPCODE==SUB  |-> (BSelector==0 && MemRD==0 && MemWD==0 && RegWrite==1 && RegSelector==2'd0));
  a_ADDI:  assert property (OPCODE==ADDI |-> (BSelector==1 && MemRD==0 && MemWD==0 && RegWrite==1 && RegSelector==2'd1));
  a_SUBI:  assert property (OPCODE==SUBI |-> (BSelector==1 && MemRD==0 && MemWD==0 && RegWrite==1 && RegSelector==2'd1));
  a_MLT :  assert property (OPCODE==MLT  |-> (BSelector==0 && MemRD==0 && MemWD==0 && RegWrite==1 && RegSelector==2'd0));
  a_MLTI:  assert property (OPCODE==MLTI |-> (BSelector==1 && MemRD==0 && MemWD==0 && RegWrite==1 && RegSelector==2'd1));
  a_AND :  assert property (OPCODE==AND  |-> (BSelector==0 && MemRD==0 && MemWD==0 && RegWrite==1 && RegSelector==2'd0));
  a_OR  :  assert property (OPCODE==OR   |-> (BSelector==0 && MemRD==0 && MemWD==0 && RegWrite==1 && RegSelector==2'd0));
  a_ANDI:  assert property (OPCODE==ANDI |-> (BSelector==1 && MemRD==0 && MemWD==0 && RegWrite==1 && RegSelector==2'd1));
  a_ORI :  assert property (OPCODE==ORI  |-> (BSelector==1 && MemRD==0 && MemWD==0 && RegWrite==1 && RegSelector==2'd1));
  a_SLR :  assert property (OPCODE==SLR  |-> (BSelector==1 && MemRD==0 && MemWD==0 && RegWrite==1 && RegSelector==2'd1));
  a_SLL :  assert property (OPCODE==SLL  |-> (BSelector==1 && MemRD==0 && MemWD==0 && RegWrite==1 && RegSelector==2'd1));
  a_LDR :  assert property (OPCODE==LDR  |-> (BSelector==1 && MemRD==1 && MemWD==0 && RegWrite==1 && RegSelector==2'd2));
  a_STR :  assert property (OPCODE==STR  |-> (BSelector==1 && MemRD==0 && MemWD==1 && RegWrite==1 && RegSelector==2'd2));
  a_BNE :  assert property (OPCODE==BNE  |-> (BSelector==0 && MemRD==0 && MemWD==0 && RegWrite==0 && RegSelector==2'd1));
  a_BEQ :  assert property (OPCODE==BEQ  |-> (BSelector==0 && MemRD==0 && MemWD==0 && RegWrite==0 && RegSelector==2'd1));
  a_J   :  assert property (OPCODE==J    |-> (BSelector==0 && MemRD==0 && MemWD==0 && RegWrite==0 && RegSelector==2'd0));
  a_CMP :  assert property (OPCODE==CMP  |-> (BSelector==0 && MemRD==0 && MemWD==0 && RegWrite==1 && RegSelector==2'd0));
  a_NOP :  assert property (OPCODE==NOP  |-> (BSelector==0 && MemRD==0 && MemWD==0 && RegWrite==0 && RegSelector==2'd0));

  // Default/illegal opcode mapping must match DUT default (NOP-like)
  a_illegal_default: assert property (
    !(OPCODE inside {ADD,SUB,ADDI,SUBI,MLT,MLTI,AND,OR,ANDI,ORI,SLR,SLL,LDR,STR,BNE,BEQ,J,CMP,NOP})
    |-> (BSelector==0 && MemRD==0 && MemWD==0 && RegWrite==0 && RegSelector==2'd0)
  );

  // PCSelect combinational function correctness (sampled on clk)
  a_pcselect_func: assert property (
    PCSelect == ((BOpCode==BNE && !Zero) || (BOpCode==BEQ && Zero))
  );
  // If PCSelect is 1, the BOpCode must be a branch
  a_pcselect_implies_branch: assert property (PCSelect |-> (BOpCode inside {BNE,BEQ}));

  // Coverage

  // Exercise every opcode
  c_ADD :  cover property (OPCODE==ADD);
  c_SUB :  cover property (OPCODE==SUB);
  c_ADDI:  cover property (OPCODE==ADDI);
  c_SUBI:  cover property (OPCODE==SUBI);
  c_MLT :  cover property (OPCODE==MLT);
  c_MLTI:  cover property (OPCODE==MLTI);
  c_AND :  cover property (OPCODE==AND);
  c_OR  :  cover property (OPCODE==OR);
  c_ANDI:  cover property (OPCODE==ANDI);
  c_ORI :  cover property (OPCODE==ORI);
  c_SLR :  cover property (OPCODE==SLR);
  c_SLL :  cover property (OPCODE==SLL);
  c_LDR :  cover property (OPCODE==LDR);
  c_STR :  cover property (OPCODE==STR);
  c_BNE :  cover property (OPCODE==BNE);
  c_BEQ :  cover property (OPCODE==BEQ);
  c_J   :  cover property (OPCODE==J);
  c_CMP :  cover property (OPCODE==CMP);
  c_NOP :  cover property (OPCODE==NOP);

  // Branch decision coverage
  c_beq_taken    : cover property (BOpCode==BEQ && Zero  && PCSelect);
  c_beq_notaken  : cover property (BOpCode==BEQ && !Zero && !PCSelect);
  c_bne_taken    : cover property (BOpCode==BNE && !Zero && PCSelect);
  c_bne_notaken  : cover property (BOpCode==BNE && Zero  && !PCSelect);
  c_pcselect_0_1 : cover property (PCSelect==1), cover property (PCSelect==0);

  // Memory paths
  c_ldr_signals: cover property (OPCODE==LDR && MemRD && !MemWD && RegSelector==2);
  c_str_signals: cover property (OPCODE==STR && MemWD && !MemRD && RegSelector==2);

  // RegSelector usage
  c_regsel0: cover property (RegSelector==2'd0);
  c_regsel1: cover property (RegSelector==2'd1);
  c_regsel2: cover property (RegSelector==2'd2);

endmodule