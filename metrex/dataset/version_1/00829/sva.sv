// SVA for pipeline_processor
// Quality-focused, concise checks and coverage

bind pipeline_processor pipeline_processor_sva();

module pipeline_processor_sva;

  // Bind target
  pipeline_processor dut();

  // Local mirrors of DUT encodings (avoid hierarchical localparam deps)
  localparam logic [1:0] ST_IF = 2'b00, ST_ID = 2'b01, ST_EX = 2'b10;
  localparam logic [5:0] ADD_OP = 6'd0, SUB_OP = 6'd1, LW_OP = 6'd2, SW_OP = 6'd3, BEQ_OP = 6'd4;

  default clocking cb @(posedge dut.clk); endclocking

  // FSM sequencing
  assert property (dut.state == ST_IF |=> dut.state == ST_ID);
  assert property (dut.state == ST_ID |=> dut.state == ST_EX);
  assert property (dut.state == ST_EX |=> dut.state == ST_IF);

  // IF stage actions (take effect next cycle)
  assert property (dut.state == ST_IF |=> dut.ID_EX_Flush == 1'b0
                                    && dut.ID_EX_IR_temp  == $past(dut.IF_ID_IR)
                                    && dut.ID_EX_NPC_temp == $past(dut.IF_ID_NPC)
                                    && dut.PC             == $past(dut.IF_ID_NPC)
                                    && dut.state          == ST_ID);

  // ID stage: field extraction (note truncation as coded)
  assert property (dut.state == ST_ID |=> dut.ID_EX_IR  == $past(dut.ID_EX_IR_temp)
                                   &&  dut.ID_EX_NPC == $past(dut.ID_EX_NPC_temp)
                                   &&  dut.ID_EX_rs  == $past(dut.ID_EX_IR_temp[25:21])
                                   &&  dut.ID_EX_rt  == $past(dut.ID_EX_IR_temp[20:16])
                                   &&  dut.ID_EX_rd  == $past(dut.ID_EX_IR_temp[15:11])
                                   &&  dut.ID_EX_imm == $past(dut.ID_EX_IR_temp[4:0])   // truncated to 5 bits
                                   &&  dut.ID_EX_func== $past(dut.ID_EX_IR_temp[4:0]));  // truncated to 5 bits

  // ID decode -> ALUOp mapping (visible at EX stage)
  assert property (dut.state == ST_ID && dut.ID_EX_IR_temp[31:26] inside {ADD_OP,SUB_OP} |=> dut.state==ST_EX && dut.ID_EX_ALUOp==3'b000);
  assert property (dut.state == ST_ID && dut.ID_EX_IR_temp[31:26] == LW_OP               |=> dut.state==ST_EX && dut.ID_EX_ALUOp==3'b001);
  assert property (dut.state == ST_ID && dut.ID_EX_IR_temp[31:26] == SW_OP               |=> dut.state==ST_EX && dut.ID_EX_ALUOp==3'b010);
  assert property (dut.state == ST_ID && dut.ID_EX_IR_temp[31:26] == BEQ_OP              |=> dut.state==ST_EX && dut.ID_EX_ALUOp==3'b100);

  // EX stage: outputs A/B and legal ALUOp
  assert property (dut.state == ST_EX |=> dut.ID_EX_A == $past(dut.ID_EX_A_temp)
                                   &&  dut.ID_EX_B == $past(dut.ID_EX_B_temp)
                                   &&  dut.state   == ST_IF);
  assert property (dut.state == ST_EX |-> dut.ID_EX_ALUOp inside {3'b000,3'b001,3'b010,3'b100});

  // EX stage: ID_EX_IR construction per ALUOp (as coded, including width truncations/zero-extend)
  assert property (dut.state==ST_EX && dut.ID_EX_ALUOp==3'b000 |=> dut.ID_EX_IR == $past({6'b000000, dut.ID_EX_rs, dut.ID_EX_rt, dut.ID_EX_rd, 5'b00000, dut.ID_EX_func}));
  assert property (dut.state==ST_EX && dut.ID_EX_ALUOp==3'b001 |=> dut.ID_EX_IR == $past({6'b100011, dut.ID_EX_rs, dut.ID_EX_rt, dut.ID_EX_imm}));
  assert property (dut.state==ST_EX && dut.ID_EX_ALUOp==3'b010 |=> dut.ID_EX_IR == $past({6'b101011, dut.ID_EX_rs, dut.ID_EX_rt, dut.ID_EX_imm}));

  // BEQ behavior (taken vs not-taken) affecting Flush and ID_EX_NPC
  assert property (dut.state==ST_EX && dut.ID_EX_ALUOp==3'b100 && (dut.ID_EX_A_temp==dut.ID_EX_B_temp)
                   |=> dut.ID_EX_Flush==1 && dut.ID_EX_NPC == $past(dut.ID_EX_NPC) + ($past(dut.ID_EX_imm) << 2));
  assert property (dut.state==ST_EX && dut.ID_EX_ALUOp==3'b100 && (dut.ID_EX_A_temp!=dut.ID_EX_B_temp)
                   |=> dut.ID_EX_Flush==0 && dut.ID_EX_NPC == $past(dut.ID_EX_NPC) + 32'd4);

  // PC update selection at EX (uses PCSrc or PRIOR flush, per nonblocking semantics)
  assert property (dut.state==ST_EX && (dut.PCSrc==1'b1 || $past(dut.ID_EX_Flush)==1'b1)
                   |=> dut.PC == $past(dut.EX_MEM_NPC));
  assert property (dut.state==ST_EX && !(dut.PCSrc==1'b1 || $past(dut.ID_EX_Flush)==1'b1)
                   |=> dut.PC == $past(dut.ID_EX_NPC));

  // Side-effect containment: arrays and outputs only change in intended ops/stages
  assert property (dut.state!=ST_EX && $past(dut.state)!=ST_EX |-> $stable(dut.ID_EX_A) && $stable(dut.ID_EX_B));
  assert property (dut.state==ST_EX && dut.ID_EX_ALUOp!=3'b010 |=> $stable(dut.mem));     // mem only on SW
  assert property (dut.state==ST_EX && !(dut.ID_EX_ALUOp inside {3'b000,3'b001}) |=> $stable(dut.reg_file)); // reg_file only on R/LW
  assert property (dut.state!=ST_EX && $past(dut.state)!=ST_EX |-> $stable(dut.mem) && $stable(dut.reg_file));

  // Data-path effects: write values (using $past for RHS sampling)
  assert property (dut.state==ST_EX && dut.ID_EX_ALUOp==3'b000
                   |=> dut.reg_file[$past(dut.ID_EX_rd)] == $past(dut.ID_EX_A_temp) + $past(dut.ID_EX_B_temp)
                    && $stable(dut.mem));
  assert property (dut.state==ST_EX && dut.ID_EX_ALUOp==3'b001
                   |=> dut.reg_file[$past(dut.ID_EX_rt)] == $past(dut.mem[$past(dut.ID_EX_A_temp)+$past(dut.ID_EX_imm)])
                    && $stable(dut.mem));
  assert property (dut.state==ST_EX && dut.ID_EX_ALUOp==3'b010
                   |=> dut.mem[$past(dut.ID_EX_A_temp)+$past(dut.ID_EX_imm)] == $past(dut.ID_EX_B_temp)
                    && $stable(dut.reg_file));

  // Coverage
  cover property (dut.state==ST_IF ##1 dut.state==ST_ID ##1 dut.state==ST_EX ##1 dut.state==ST_IF);
  cover property (dut.state==ST_EX && dut.ID_EX_ALUOp==3'b000);
  cover property (dut.state==ST_EX && dut.ID_EX_ALUOp==3'b001);
  cover property (dut.state==ST_EX && dut.ID_EX_ALUOp==3'b010);
  cover property (dut.state==ST_EX && dut.ID_EX_ALUOp==3'b100 && dut.ID_EX_A_temp==dut.ID_EX_B_temp); // BEQ taken
  cover property (dut.state==ST_EX && dut.ID_EX_ALUOp==3'b100 && dut.ID_EX_A_temp!=dut.ID_EX_B_temp); // BEQ not taken
  cover property (dut.state==ST_EX && dut.PCSrc==1'b1);                     // PC override via PCSrc
  cover property (dut.state==ST_EX && $past(dut.ID_EX_Flush)==1'b1);        // PC override via prior Flush

endmodule