module InstrDecod(instr, pc, regWrite, writeData, writeRegister, opcode, funct, regOut1, regOut2, regRt, regRd, immValue, jumpDest, branchDest);
  input [31:0] instr;    input [31:0] pc; input [31:0] writeData; input [4:0] writeRegister; input regWrite;   output [5:0] opcode; output [5:0] funct;  output [31:0] regOut1; output [31:0] regOut2; output [4:0] regRt;  output [4:0] regRd;  output [31:0] jumpDest;  output [31:0] immValue; output [31:0] branchDest; reg signed [31:0] registerMem [0:31];

  wire signed [31:0] writeData;
  wire signed [31:0] pc;
  reg [5:0] opcode, funct;
  reg [4:0] regRs, regRt, regRd;
  reg signed [31:0] regOut1, regOut2;
  reg signed [31:0] immValue, jumpDest, branchDest;
  reg signed [31:0] signedBranch;


  integer idx;
  initial
    begin
    for (idx = 0; idx < 32; idx = idx + 1)
      begin
        registerMem[idx] = 0;
      end
  end

  always @(*) begin
    if (regWrite == 1)
      registerMem[writeRegister] = writeData;
  end

  always @(instr) begin
    opcode = instr[31:26];
     funct = instr[5:0];

    regRs = instr[25:21];
    regRt = instr[20:16];
    regRd = instr[15:11];

    immValue = { {16{instr[15]}}, instr[15:0] };

    jumpDest = { {5{instr[25]}}, instr[25:0] };

    signedBranch = { {16{instr[15]}}, instr[15:0] };
    branchDest = pc + signedBranch;

    regOut1 = registerMem[regRs];
    regOut2 = registerMem[regRt];
  end
  
endmodule
