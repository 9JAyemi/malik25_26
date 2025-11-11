// Bind these SVA into the DUT scope
bind alu_4bit alu_4bit_sva sva();

module alu_4bit_sva;
  // Sample on any input change; ignore unknown inputs
  default clocking cb @ (posedge ($changed({A,B,OP}))); endclocking
  default disable iff ($isunknown({A,B,OP}));

  // Internal pipeline consistency
  a_pipe1: assert property (alu_out2 == alu_out1);
  a_pipe2: assert property (result  == alu_out2);

  // Functional correctness per opcode
  a_add: assert property ((OP==3'b000) |-> result == (A + B));
  a_sub: assert property ((OP==3'b001) |-> result == (A - B));
  a_and: assert property ((OP==3'b010) |-> result == (A & B));
  a_or:  assert property ((OP==3'b011) |-> result == (A | B));
  a_xor: assert property ((OP==3'b100) |-> result == (A ^ B));
  a_sll: assert property ((OP==3'b101) |-> result == {A[2:0],1'b0});
  a_def: assert property ((OP inside {3'b110,3'b111}) |-> result == 4'b0);

  // Result must be known when inputs are known
  a_no_x: assert property (!$isunknown(result));

  // Output changes only when inputs change (no spurious glitches observed)
  a_no_spurious_change: assert property (@(posedge ($changed(result))) $changed({A,B,OP}));

  // Functional coverage
  c_add: cover property (OP==3'b000);
  c_sub: cover property (OP==3'b001);
  c_and: cover property (OP==3'b010);
  c_or:  cover property (OP==3'b011);
  c_xor: cover property (OP==3'b100);
  c_sll: cover property (OP==3'b101);
  c_def: cover property (OP inside {3'b110,3'b111});
  c_add_carry:   cover property ((OP==3'b000) && ({1'b0,A}+{1'b0,B})[4]);
  c_sub_borrow:  cover property ((OP==3'b001) && ({1'b0,A}-{1'b0,B})[4]);
  c_sll_dropMSB: cover property ((OP==3'b101) && A[3] && (result[0]==1'b0));
endmodule