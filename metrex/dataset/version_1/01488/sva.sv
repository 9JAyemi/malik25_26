// SVA for Controller
// Binds a golden decode check, key invariants, and compact functional coverage.

module Controller_sva(
  input  logic        clk,
  input  logic        rst,
  input  logic        RdOrR2, AluOrMem, RFWE, MWE,
  input  logic [1:0]  stackContrl, pcContrl,
  input  logic        Zero, Cout,
  input  logic [5:0]  cntlInstruc
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Golden decode function (mirrors DUT’s priority and mapping)
  function automatic logic [7:0] ctrl_f(logic Zero_i, logic Cout_i, logic [5:0] instr);
    logic        RdOrR2_i, AluOrMem_i, RFWE_i, MWE_i;
    logic [1:0]  stack_i, pc_i;
    begin
      if ((instr[5] == 1'b0) || (instr[5:3] == 3'b110)) begin
        RdOrR2_i=1'b0; AluOrMem_i=1'b1; RFWE_i=1'b1; MWE_i=1'b0; stack_i=2'b00; pc_i=2'b00;
      end else if (instr[5:1] == 5'b10000) begin
        RdOrR2_i=1'b0; AluOrMem_i=1'b0; RFWE_i=1'b1; MWE_i=1'b0; stack_i=2'b00; pc_i=2'b00;
      end else if (instr[5:1] == 5'b10001) begin
        RdOrR2_i=1'b1; AluOrMem_i=1'b1; RFWE_i=1'b0; MWE_i=1'b1; stack_i=2'b00; pc_i=2'b00;
      end else if (instr[5:3] == 3'b101) begin
        RdOrR2_i=1'b0; AluOrMem_i=1'b1; RFWE_i=1'b0; MWE_i=1'b0; stack_i=2'b00;
        unique case (instr[2:1])
          2'b00: pc_i =  Zero_i   ? 2'b01 : 2'b00;
          2'b01: pc_i = ~Zero_i   ? 2'b01 : 2'b00;
          2'b10: pc_i =  Cout_i   ? 2'b01 : 2'b00;
          default: pc_i = ~Cout_i ? 2'b01 : 2'b00; // 2'b11
        endcase
      end else if (instr[5:1] == 5'b11100) begin
        RdOrR2_i=1'b0; AluOrMem_i=1'b1; RFWE_i=1'b0; MWE_i=1'b0; stack_i=2'b00; pc_i=2'b11;
      end else if (instr[5:1] == 5'b11101) begin
        RdOrR2_i=1'b0; AluOrMem_i=1'b1; RFWE_i=1'b0; MWE_i=1'b0; stack_i=2'b01; pc_i=2'b11;
      end else if (instr[5:0] == 6'b111100) begin
        RdOrR2_i=1'b0; AluOrMem_i=1'b1; RFWE_i=1'b0; MWE_i=1'b0; stack_i=2'b10; pc_i=2'b10;
      end else begin
        RdOrR2_i=1'b0; AluOrMem_i=1'b0; RFWE_i=1'b0; MWE_i=1'b0; stack_i=2'b00; pc_i=2'b00;
      end
      ctrl_f = {RdOrR2_i, AluOrMem_i, RFWE_i, MWE_i, stack_i, pc_i};
    end
  endfunction

  // Bundle for convenience
  wire [7:0] dut_ctrl = {RdOrR2, AluOrMem, RFWE, MWE, stackContrl, pcContrl};

  // 1) Golden decode equivalence (primary check)
  assert property (dut_ctrl == ctrl_f(Zero, Cout, cntlInstruc))
    else $error("Controller decode mismatch: instr=%b Z=%0b C=%0b got=%b exp=%b",
                cntlInstruc, Zero, Cout, dut_ctrl, ctrl_f(Zero, Cout, cntlInstruc));

  // 2) No X/Z on outputs
  assert property (!$isunknown(dut_ctrl))
    else $error("Controller outputs contain X/Z: %b", dut_ctrl);

  // 3) Targeted invariants (helpful for debug, concise)
  // Store is the only case that asserts MWE and RdOrR2
  assert property (MWE |-> (cntlInstruc[5:1] == 5'b10001));
  assert property (RdOrR2 |-> (cntlInstruc[5:1] == 5'b10001));

  // pcContrl uniqueness mapping
  assert property (pcContrl == 2'b01 |->
                   (cntlInstruc[5:3] == 3'b101) &&
                   ((cntlInstruc[2:1]==2'b00 &&  Zero) ||
                    (cntlInstruc[2:1]==2'b01 && ~Zero) ||
                    (cntlInstruc[2:1]==2'b10 &&  Cout) ||
                    (cntlInstruc[2:1]==2'b11 && ~Cout))));
  assert property (pcContrl == 2'b11 |->
                   (cntlInstruc[5:1] == 5'b11100 || cntlInstruc[5:1] == 5'b11101));
  assert property (pcContrl == 2'b10 |->
                   (cntlInstruc[5:0] == 6'b111100));

  // RFWE asserted only in ALU/writeback or load
  assert property (RFWE |-> ((cntlInstruc[5]==1'b0) || (cntlInstruc[5:3]==3'b110) ||
                             (cntlInstruc[5:1]==5'b10000)));

  // stackContrl uniqueness for nonzero values
  assert property ((stackContrl == 2'b01) |->
                   (cntlInstruc[5:1] == 5'b11101));
  assert property ((stackContrl == 2'b10) |->
                   (cntlInstruc[5:0] == 6'b111100));

  // 4) Functional coverage (decode classes + branch taken/not-taken)
  // ALU/writeback class
  cover property (cntlInstruc[5] == 1'b0);
  cover property (cntlInstruc[5:3] == 3'b110);

  // Load / Store
  cover property (cntlInstruc[5:1] == 5'b10000);
  cover property (cntlInstruc[5:1] == 5'b10001);

  // Conditional branch subops: taken and not-taken
  cover property ((cntlInstruc[5:3]==3'b101) && (cntlInstruc[2:1]==2'b00) &&  Zero);
  cover property ((cntlInstruc[5:3]==3'b101) && (cntlInstruc[2:1]==2'b00) && ~Zero);
  cover property ((cntlInstruc[5:3]==3'b101) && (cntlInstruc[2:1]==2'b01) && ~Zero);
  cover property ((cntlInstruc[5:3]==3'b101) && (cntlInstruc[2:1]==2'b01) &&  Zero);
  cover property ((cntlInstruc[5:3]==3'b101) && (cntlInstruc[2:1]==2'b10) &&  Cout);
  cover property ((cntlInstruc[5:3]==3'b101) && (cntlInstruc[2:1]==2'b10) && ~Cout);
  cover property ((cntlInstruc[5:3]==3'b101) && (cntlInstruc[2:1]==2'b11) && ~Cout);
  cover property ((cntlInstruc[5:3]==3'b101) && (cntlInstruc[2:1]==2'b11) &&  Cout);

  // Unconditional control-flow ops
  cover property (cntlInstruc[5:1] == 5'b11100);
  cover property (cntlInstruc[5:1] == 5'b11101);
  cover property (cntlInstruc[5:0] == 6'b111100);

  // Default (none of the above)
  cover property (!( (cntlInstruc[5]==1'b0) ||
                     (cntlInstruc[5:3]==3'b110) ||
                     (cntlInstruc[5:1]==5'b10000) ||
                     (cntlInstruc[5:1]==5'b10001) ||
                     (cntlInstruc[5:3]==3'b101)  ||
                     (cntlInstruc[5:1]==5'b11100)||
                     (cntlInstruc[5:1]==5'b11101)||
                     (cntlInstruc[5:0]==6'b111100)));

  // Output value coverage (exercise all encodings)
  cover property (pcContrl == 2'b00);
  cover property (pcContrl == 2'b01);
  cover property (pcContrl == 2'b10);
  cover property (pcContrl == 2'b11);

  cover property (stackContrl == 2'b00);
  cover property (stackContrl == 2'b01);
  cover property (stackContrl == 2'b10);

  cover property (MWE);
  cover property (RFWE);

endmodule

bind Controller Controller_sva sva_inst(.*);