// Bind these SVA to the DUT
bind InstrDecod InstrDecod_sva sva();

module InstrDecod_sva;

  // Local assertion clock: toggles on relevant activity
  logic sva_clk;
  initial sva_clk = 0;
  always @(instr or pc or regWrite or writeRegister or writeData
           or opcode or funct or regOut1 or regOut2 or regRt or regRd
           or immValue or jumpDest or branchDest)
    sva_clk <= ~sva_clk;

  default clocking cb @(posedge sva_clk); endclocking

  // Field extraction from instr
  assert property (disable iff ($isunknown(instr))) opcode == instr[31:26];
  assert property (disable iff ($isunknown(instr))) funct  == instr[5:0];
  assert property (disable iff ($isunknown(instr))) regRt  == instr[20:16];
  assert property (disable iff ($isunknown(instr))) regRd  == instr[15:11];
  assert property (disable iff ($isunknown(instr))) regRs  == instr[25:21];

  // Sign-extends and derived addresses
  assert property (disable iff ($isunknown(instr))) immValue     == {{16{instr[15]}}, instr[15:0]};
  assert property (disable iff ($isunknown(instr))) signedBranch == {{16{instr[15]}}, instr[15:0]};
  assert property (disable iff ($isunknown(instr))) jumpDest     == {{5{instr[25]}},  instr[25:0]};
  assert property (disable iff ($isunknown({instr,pc})))
    branchDest == $signed(pc) + $signed({{16{instr[15]}}, instr[15:0]});

  // Register file readouts match selected addresses
  assert property (disable iff ($initstate || $isunknown(instr))) regOut1 == registerMem[regRs];
  assert property (disable iff ($initstate || $isunknown(instr))) regOut2 == registerMem[regRt];

  // Outputs not X when inputs are known
  assert property (disable iff ($initstate)) (!$isunknown({instr,pc})) |-> !$isunknown({opcode,funct,regRt,regRd,immValue,jumpDest,branchDest});

  // Register file write semantics and stability
  genvar gi;
  generate
    for (gi=0; gi<32; gi++) begin : REGFILE_CHECKS
      localparam [4:0] IDX = gi[4:0];

      // Write hits target element immediately
      assert property (disable iff ($initstate || $isunknown({regWrite,writeRegister,writeData})))
        (regWrite && writeRegister==IDX) |-> (registerMem[gi] == writeData);

      // Non-target elements do not change during a write
      assert property (disable iff ($initstate || $isunknown({regWrite,writeRegister,writeData})))
        (regWrite && writeRegister!=IDX) |-> $stable(registerMem[gi]);

      // With no write, all elements remain stable
      assert property (disable iff ($initstate || $isunknown(regWrite)))
        (!regWrite) |=> $stable(registerMem[gi]);
    end
  endgenerate

  // Functional coverage
  cover property (opcode == 6'd0);                   // R-type
  cover property (opcode != 6'd0);                   // non R-type
  cover property (instr[15] && immValue[31]);        // negative imm sign-extended
  cover property (!instr[15] && !immValue[31]);      // positive imm sign-extended
  cover property (instr[25] && &jumpDest[31:27]);    // jumpDest high bits all ones
  cover property (regWrite && writeRegister==5'd0);  // write reg 0
  cover property (regWrite && writeRegister==5'd31); // write reg 31
  cover property (regWrite && (writeRegister==regRs || writeRegister==regRt)); // RAW scenario

endmodule