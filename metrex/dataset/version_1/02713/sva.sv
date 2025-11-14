// SVA for opcode_decoder
module opcode_decoder_sva (
  input logic        CCLK,
  input logic        rst,
  input logic [31:0] instr,
  input logic [7:0]  IF
);
  default clocking cb @(posedge CCLK); endclocking

  // Opcodes / functs
  localparam logic [5:0] OP_R    = 6'b000000;
  localparam logic [5:0] OP_ADDI = 6'b001000;
  localparam logic [5:0] OP_ANDI = 6'b001100;
  localparam logic [5:0] OP_ORI  = 6'b001101;
  localparam logic [5:0] OP_LW   = 6'b100011;
  localparam logic [5:0] OP_SW   = 6'b101011;
  localparam logic [5:0] OP_BEQ  = 6'b000100;
  localparam logic [5:0] OP_BNE  = 6'b000101;
  localparam logic [5:0] OP_J    = 6'b000010;

  localparam logic [5:0] F_ADD = 6'b100000;
  localparam logic [5:0] F_SUB = 6'b100010;
  localparam logic [5:0] F_AND = 6'b100100;
  localparam logic [5:0] F_OR  = 6'b100101;
  localparam logic [5:0] F_SLL = 6'b000000;
  localparam logic [5:0] F_SRL = 6'b000010;
  localparam logic [5:0] F_SRA = 6'b000011;

  // Basic sanity
  assert property (@(posedge CCLK) IF inside {[8'd0:8'd15]});
  assert property (@(posedge CCLK) !$isunknown(IF));

  // Reset effect (must hold even during reset cycle)
  assert property (@(posedge CCLK) rst |-> IF == 8'd0);

  // R-type decodes
  assert property (disable iff (rst) (instr[31:26]==OP_R && instr[5:0]==F_ADD) |-> 
                   IF == ((|instr[15:11]) ? 8'd1 : 8'd0));
  assert property (disable iff (rst) (instr[31:26]==OP_R && instr[5:0]==F_SUB) |-> IF==8'd2);
  assert property (disable iff (rst) (instr[31:26]==OP_R && instr[5:0]==F_AND) |-> IF==8'd3);
  assert property (disable iff (rst) (instr[31:26]==OP_R && instr[5:0]==F_OR ) |-> IF==8'd4);
  assert property (disable iff (rst) (instr[31:26]==OP_R && instr[5:0]==F_SLL) |-> IF==8'd5);
  assert property (disable iff (rst) (instr[31:26]==OP_R && instr[5:0]==F_SRL) |-> IF==8'd6);
  assert property (disable iff (rst) (instr[31:26]==OP_R && instr[5:0]==F_SRA) |-> IF==8'd7);

  // I/J-type decodes
  assert property (disable iff (rst) (instr[31:26]==OP_ADDI) |-> IF==8'd8);
  assert property (disable iff (rst) (instr[31:26]==OP_ANDI) |-> IF==8'd9);
  assert property (disable iff (rst) (instr[31:26]==OP_ORI ) |-> IF==8'd10);
  assert property (disable iff (rst) (instr[31:26]==OP_LW  ) |-> IF==8'd11);
  assert property (disable iff (rst) (instr[31:26]==OP_SW  ) |-> IF==8'd12);
  assert property (disable iff (rst) (instr[31:26]==OP_BEQ ) |-> IF==8'd13);
  assert property (disable iff (rst) (instr[31:26]==OP_BNE ) |-> IF==8'd14);
  assert property (disable iff (rst) (instr[31:26]==OP_J   ) |-> IF==8'd15);

  // Default at top-level case for non-listed opcodes (excluding OP_R branch)
  assert property (disable iff (rst)
                   !(instr[31:26] inside {OP_R,OP_ADDI,OP_ANDI,OP_ORI,OP_LW,OP_SW,OP_BEQ,OP_BNE,OP_J})
                   |-> IF==8'd0);

  // R-type: unlisted funct holds previous IF (no assignment in DUT)
  assert property (disable iff (rst)
                   (instr[31:26]==OP_R && !(instr[5:0] inside {F_ADD,F_SUB,F_AND,F_OR,F_SLL,F_SRL,F_SRA}))
                   |-> IF==$past(IF));

  // Coverage: each decode and key branches
  cover property (rst && IF==8'd0);

  cover property (instr[31:26]==OP_R && instr[5:0]==F_ADD &&  (|instr[15:11]) && IF==8'd1);
  cover property (instr[31:26]==OP_R && instr[5:0]==F_ADD && !(|instr[15:11]) && IF==8'd0);

  cover property (instr[31:26]==OP_R && instr[5:0]==F_SUB && IF==8'd2);
  cover property (instr[31:26]==OP_R && instr[5:0]==F_AND && IF==8'd3);
  cover property (instr[31:26]==OP_R && instr[5:0]==F_OR  && IF==8'd4);
  cover property (instr[31:26]==OP_R && instr[5:0]==F_SLL && IF==8'd5);
  cover property (instr[31:26]==OP_R && instr[5:0]==F_SRL && IF==8'd6);
  cover property (instr[31:26]==OP_R && instr[5:0]==F_SRA && IF==8'd7);

  cover property (instr[31:26]==OP_ADDI && IF==8'd8);
  cover property (instr[31:26]==OP_ANDI && IF==8'd9);
  cover property (instr[31:26]==OP_ORI  && IF==8'd10);
  cover property (instr[31:26]==OP_LW   && IF==8'd11);
  cover property (instr[31:26]==OP_SW   && IF==8'd12);
  cover property (instr[31:26]==OP_BEQ  && IF==8'd13);
  cover property (instr[31:26]==OP_BNE  && IF==8'd14);
  cover property (instr[31:26]==OP_J    && IF==8'd15);

  cover property (!(instr[31:26] inside {OP_R,OP_ADDI,OP_ANDI,OP_ORI,OP_LW,OP_SW,OP_BEQ,OP_BNE,OP_J}) && IF==8'd0);
  cover property (instr[31:26]==OP_R && !(instr[5:0] inside {F_ADD,F_SUB,F_AND,F_OR,F_SLL,F_SRL,F_SRA}) && IF==$past(IF));
endmodule

// Example bind:
// bind opcode_decoder opcode_decoder_sva sva (.CCLK(CCLK), .rst(rst), .instr(instr), .IF(IF));