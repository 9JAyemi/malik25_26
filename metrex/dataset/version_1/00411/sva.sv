// SVA checks and covers for MAIN, register, and ALU
// Focused, concise, high-quality assertions

// ------------- register SVA (binds to module definition) -------------
module register_sva;
  // This bound module lives in the scope of each 'register' instance.
  // We can directly reference clk, Reset, Write_Reg, addresses, data, and REGISTERS[].
  default clocking cb @(posedge clk); endclocking

  // X checks on controls/addresses; W_Data must be known when writing
  assert property (!$isunknown({Reset, Write_Reg, R_Addr_A, R_Addr_B, W_Addr}));
  assert property (Write_Reg |-> !$isunknown(W_Data));

  // Reset clears the whole array next cycle
  genvar i;
  generate
    for (i=0; i<32; i++) begin : g_rst_clear
      assert property (Reset |=> REGISTERS[i] == 32'h0);
    end
  endgenerate

  // Read ports mirror array
  assert property (R_Data_A == REGISTERS[R_Addr_A]);
  assert property (R_Data_B == REGISTERS[R_Addr_B]);

  // Write happens (observed next cycle)
  assert property (!Reset && Write_Reg |=> REGISTERS[$past(W_Addr)] == $past(W_Data));

  // When not writing (and not in Reset), no location changes
  generate
    for (i=0; i<32; i++) begin : g_no_write_hold
      assert property (!Reset && !Write_Reg |=> $stable(REGISTERS[i]));
    end
  endgenerate

  // Covers
  cover property (Reset);
  cover property (!Reset && Write_Reg);
  cover property (!Reset ##1 Write_Reg ##1 (R_Addr_A == $past(W_Addr)) && (R_Data_A == REGISTERS[R_Addr_A]));
endmodule

bind register register_sva reg_chk();

// ------------- ALU SVA (binds to module definition; needs a clock) -------------
module ALU_sva(input logic clk);
  // Bound inside ALU instance; can directly reference A,B,F,ZF,OF,ALU_OP.
  default clocking cb @(posedge clk); endclocking

  // X checks
  assert property (!$isunknown({ALU_OP, A, B}));
  assert property (!$isunknown({F, ZF, OF}));

  // Zero flag correctness
  assert property (ZF == (F == 32'd0));

  // Logical ops
  assert property ((ALU_OP==3'd0) |-> (F == (A & B) && OF==1'b0));
  assert property ((ALU_OP==3'd1) |-> (F == (A | B) && OF==1'b0));
  assert property ((ALU_OP==3'd2) |-> (F == (A ^ B) && OF==1'b0));

  // A + 1 (note: matches DUT's OF formula using B[31])
  let add1 = {1'b0, A} + 33'd1;
  assert property ((ALU_OP==3'd3) |-> (F == add1[31:0] &&
                                       OF == (A[31] ^ B[31] ^ add1[31] ^ add1[32])));

  // A + B
  let addAB = {1'b0, A} + {1'b0, B};
  assert property ((ALU_OP==3'd4) |-> (F == addAB[31:0] &&
                                       OF == (A[31] ^ B[31] ^ addAB[31] ^ addAB[32])));

  // A - B
  let subAB = {1'b0, A} - {1'b0, B};
  assert property ((ALU_OP==3'd5) |-> (F == subAB[31:0] &&
                                       OF == (A[31] ^ B[31] ^ subAB[31] ^ subAB[32])));

  // SLT (unsigned compare per RTL)
  assert property ((ALU_OP==3'd6) |-> (F == (A < B ? 32'd1 : 32'd0) && OF==1'b0));

  // Shift left
  assert property ((ALU_OP==3'd7) |-> (F == (B << A) && OF==1'b0));

  // Op coverage
  cover property (ALU_OP==3'd0);
  cover property (ALU_OP==3'd1);
  cover property (ALU_OP==3'd2);
  cover property (ALU_OP==3'd3);
  cover property (ALU_OP==3'd4);
  cover property (ALU_OP==3'd5);
  cover property (ALU_OP==3'd6);
  cover property (ALU_OP==3'd7);
  cover property ((ALU_OP inside {3'd4,3'd5}) && OF); // overflow seen
  cover property (ZF && F==32'd0);
  cover property (!ZF && F!=32'd0);
endmodule

// Bind ALU SVA to every ALU, sampling on MAIN's clk (adjust path if needed)
bind ALU ALU_sva alu_chk(.clk($root.MAIN.clk));

// ------------- MAIN SVA (wiring/connectivity; binds to instance) -------------
module MAIN_sva;
  default clocking cb @(posedge clk); endclocking

  // Top-level X checks
  assert property (!$isunknown({Reset, Write_Reg, ALU_OP, R_Addr_A, R_Addr_B, W_Addr}));

  // Connectivity: REG <-> MAIN <-> ALU
  assert property (A == REG.R_Data_A);
  assert property (B == REG.R_Data_B);
  assert property (REG.W_Data == LED);

  assert property (ALUP.A == A);
  assert property (ALUP.B == B);
  assert property (ALUP.ALU_OP == ALU_OP);
  assert property (LED == ALUP.F);
  assert property (ZF == ALUP.ZF);
  assert property (OF == ALUP.OF);

  // Basic top-level covers
  cover property (Reset);
  cover property (!Reset && Write_Reg);
  cover property (!Reset ##1 (ALU_OP==3'd6) && (A < B) && (LED==32'd1));
endmodule

bind MAIN MAIN_sva main_chk();