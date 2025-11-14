// SVA for MEM hierarchy
// Bind into top-level MEM
module MEM_SVA (
  input  logic        clk,
  input  logic [5:0]  Op,
  input  logic [2:0]  Condition,
  input  logic        Branch,
  input  logic        MemWrite,
  input  logic        RegWrite,
  input  logic [31:0] MemData,        // store data in
  input  logic        Less, Zero, Overflow,
  input  logic [31:0] WBData,         // address
  input  logic [31:0] MemData_Mem,    // load data out (post mem_shifter)
  input  logic [3:0]  Rd_write_byte_en,
  input  logic        RegWriteValid,
  input  logic        BranchValid,
  input  logic [3:0]  Mem_write_byte_en,
  input  logic [31:0] Mem_data_in,    // reg_shifter -> Mem
  input  logic [31:0] Mem_data_out    // Mem -> mem_shifter
);
  default clocking cb @(posedge clk); endclocking
  localparam logic [5:0] OP_SW = 6'b101011;
  localparam logic [5:0] OP_LW = 6'b100011;

  // ConditionCheck
  assert property (Branch==1'b0 |-> BranchValid==1'b0);
  assert property (Branch==1'b1 |-> (
      (Condition==3'b000) ? (BranchValid==1'b0) :
      (Condition==3'b001) ? (BranchValid==     Zero) :
      (Condition==3'b010) ? (BranchValid==    !Zero) :
      (Condition==3'b011) ? (BranchValid==(Less|Zero)) :
      (Condition==3'b100) ? (BranchValid==      Less) :
      (Condition==3'b101) ? (BranchValid==     !Less) :
      (Condition==3'b110) ? (BranchValid==!(Less|Zero)) :
                            (BranchValid==1'b0) // 3'b111
  ));
  assert property (RegWriteValid == (RegWrite && !Overflow));

  // reg_shifter (write path)
  assert property (MemWrite==1'b0 |-> Mem_write_byte_en==4'b0000);
  assert property (MemWrite==1'b1 |-> Mem_write_byte_en ==
    (Op==OP_SW ? 4'b1111 :
     (WBData[1:0]==2'b00) ? 4'b1000 :
     (WBData[1:0]==2'b01) ? 4'b1100 :
     (WBData[1:0]==2'b10) ? 4'b1110 : 4'b1111));

  assert property ((Op==OP_SW) |-> (Mem_data_in==MemData));
  assert property ((Op!=OP_SW) |-> (
    (WBData[1:0]==2'b00) ? (Mem_data_in=={MemData[7:0],  24'b0}) :
    (WBData[1:0]==2'b01) ? (Mem_data_in=={MemData[15:0], 16'b0}) :
    (WBData[1:0]==2'b10) ? (Mem_data_in=={MemData[23:0],  8'b0}) :
                           (Mem_data_in== MemData)));

  // mem_shifter (read path)
  assert property ((Op==OP_LW) |-> (MemData_Mem==Mem_data_out && Rd_write_byte_en==4'b1111));
  assert property ((Op!=OP_LW) |-> (
    (WBData[1:0]==2'b00) ? (MemData_Mem==Mem_data_out                     && Rd_write_byte_en==4'b1111) :
    (WBData[1:0]==2'b01) ? (MemData_Mem=={Mem_data_out[23:0], 8'b0}       && Rd_write_byte_en==4'b1110) :
    (WBData[1:0]==2'b10) ? (MemData_Mem=={Mem_data_out[15:0], 16'b0}      && Rd_write_byte_en==4'b1100) :
                           (MemData_Mem=={Mem_data_out[7:0],  24'b0}      && Rd_write_byte_en==4'b1000)));

  // Mem boundary behavior
  assert property ( {WBData[31:2],2'b00} >= 32'd496 |-> Mem_data_out==32'h0000_0000 );

  // Functional coverage
  cover property (Branch && Condition==3'b001 &&  Zero);
  cover property (Branch && Condition==3'b010 && !Zero);
  cover property (Branch && Condition==3'b011 && (Less||Zero));
  cover property (Branch && Condition==3'b100 &&  Less);
  cover property (Branch && Condition==3'b101 && !Less);
  cover property (Branch && Condition==3'b110 && !Less && !Zero);
  cover property (Branch && (Condition==3'b000 || Condition==3'b111) && !BranchValid);

  cover property ( RegWrite && !Overflow &&  RegWriteValid);
  cover property ( RegWrite &&  Overflow && !RegWriteValid);
  cover property (!RegWrite && !RegWriteValid);

  cover property (MemWrite && Op==OP_SW  && WBData[1:0]==2'b00);
  cover property (MemWrite && Op==OP_SW  && WBData[1:0]==2'b01);
  cover property (MemWrite && Op==OP_SW  && WBData[1:0]==2'b10);
  cover property (MemWrite && Op==OP_SW  && WBData[1:0]==2'b11);

  cover property (Op==OP_LW && WBData[1:0]==2'b00);
  cover property (Op==OP_LW && WBData[1:0]==2'b01);
  cover property (Op==OP_LW && WBData[1:0]==2'b10);
  cover property (Op==OP_LW && WBData[1:0]==2'b11);

  cover property ( {WBData[31:2],2'b00} >= 32'd496 );
  cover property ( {WBData[31:2],2'b00} <  32'd496 );
endmodule

bind MEM MEM_SVA u_MEM_SVA (
  .clk(clk),
  .Op(Op),
  .Condition(Condition),
  .Branch(Branch),
  .MemWrite(MemWrite),
  .RegWrite(RegWrite),
  .MemData(MemData),
  .Less(Less), .Zero(Zero), .Overflow(Overflow),
  .WBData(WBData),
  .MemData_Mem(MemData_Mem),
  .Rd_write_byte_en(Rd_write_byte_en),
  .RegWriteValid(RegWriteValid),
  .BranchValid(BranchValid),
  .Mem_write_byte_en(Mem_write_byte_en),
  .Mem_data_in(Mem_data_in),
  .Mem_data_out(Mem_data_out)
);