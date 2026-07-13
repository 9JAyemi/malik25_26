


module control(op, alu_op, regDst, aluSrc, memToReg, regWrite, memRead, memWrite, branch);
  
  input [5:0] op;
  
  output [1:0] alu_op;
  
  output regDst;
  
  output aluSrc;
  
  output memToReg;
  
  output regWrite;
  
  output memRead;
  
  output memWrite;
  
  output branch;
  
  wire int0;
  
  wire op0_bar;
  
  wire op1_bar;
  
  wire op2_bar;
  
  wire op3_bar;
  
  wire op4_bar;
  
  wire op5_bar;
  
  wire _00_;
  
  wire _01_;
  
  wire _02_;
  
  wire _03_;
  
  wire _04_;
  
  wire _05_;
  
  wire _06_;
  
  wire _07_;
  
  wire _08_;
  
  wire _09_;
  
  wire _10_;
  
  wire _11_;
  
  wire _12_;
  
  wire _13_;
  
  wire _14_;
  assign op0_bar = ~op[0];
  assign op1_bar = ~op[1];
  assign op2_bar = ~op[2];
  assign op3_bar = ~op[3];
  assign op4_bar = ~op[4];
  assign op5_bar = ~op[5];
  assign _00_ = op5_bar & op4_bar;
  assign _01_ = _00_ & op3_bar;
  assign _02_ = _01_ & op[2];
  assign _03_ = _02_ & op1_bar;
  assign alu_op[0] = _03_ & op0_bar;
  assign _04_ = _01_ & op2_bar;
  assign _05_ = _04_ & op1_bar;
  assign alu_op[1] = _05_ & op0_bar;
  assign _06_ = op[5] & op4_bar;
  assign _07_ = _06_ & op3_bar;
  assign _08_ = _07_ & op2_bar;
  assign _09_ = _08_ & op[1];
  assign int0 = _09_ & op[0];
  assign _10_ = _06_ & op[3];
  assign _11_ = _10_ & op2_bar;
  assign _12_ = _11_ & op[1];
  assign memWrite = _12_ & op[0];
  assign _13_ = _06_ & op2_bar;
  assign _14_ = _13_ & op[1];
  assign aluSrc = _14_ & op[0];
  assign regWrite = int0 | alu_op[1];
  assign regDst = alu_op[1];
  assign memToReg = int0;
  assign memRead = int0;
  assign branch = alu_op[0];
endmodule
