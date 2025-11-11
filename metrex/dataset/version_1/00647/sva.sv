// SVA for RIPPLEADD_64 and FULLADDER_1BIT
// Use any free-running sampling clock (connect via bind)

module RIPPLEADD_64_SVA(input logic clk);
  default clocking cb @ (posedge clk); endclocking

  // Basic sanity on inputs/outputs
  assume property (1 |-> ##0 !$isunknown({A,B,Cin}));
  assert property (1 |-> ##0 !$isunknown({S,Cout}));

  // Golden functionality: 65-bit sum must match
  assert property (1 |-> ##0 {Cout,S} == A + B + Cin);

  // Carry chain wiring
  assert property (1 |-> ##0 C[0] == Cin);
  genvar i;
  generate
    for (i=0; i<63; i++) begin : g_chk
      assert property (1 |-> ##0 S[i]     == (A[i] ^ B[i] ^ C[i]));
      assert property (1 |-> ##0 C[i+1]   == ((A[i] & B[i]) | (C[i] & (A[i] ^ B[i]))));
    end
  endgenerate

  // MSB stage should be a full-adder (these will flag the missing MSB FA)
  assert property (1 |-> ##0 S[63]  == (A[63] ^ B[63] ^ C[63]));
  assert property (1 |-> ##0 Cout   == ((A[63] & B[63]) | (C[63] & (A[63] ^ B[63]))));

  // Useful covers
  cover property (1 |-> ##0 ({A,B,Cin} == '0));                         // zero + zero
  cover property (1 |-> ##0 (A == '1 && B == '0 && Cin));               // full ripple case
  cover property (1 |-> ##0 (A == '1 && B == '0 && !Cin));              // no carry out, all-ones pass
  cover property (1 |-> ##0 (A == '1 && B == '1 && !Cin));              // large generate at many bits
  cover property (1 |-> ##0 (Cout && (S == '0)));                       // all-ones + 1
endmodule


module FULLADDER_1BIT_SVA(input logic clk);
  default clocking cb @ (posedge clk); endclocking
  assume property (1 |-> ##0 !$isunknown({A,B,Cin}));
  assert property (1 |-> ##0 {Cout,S} == A + B + Cin);

  // Minimal functional coverage across key classes
  cover property (1 |-> ##0 ({A,B,Cin} == 3'b000)); // kill
  cover property (1 |-> ##0 ({A,B,Cin} == 3'b011)); // propagate with Cin=1
  cover property (1 |-> ##0 ({A,B,Cin} == 3'b110)); // generate
  cover property (1 |-> ##0 ({A,B,Cin} == 3'b101)); // mixed
endmodule


// Example binds (connect an existing free-running clock)
// replace 'clk' with your environment clock
bind RIPPLEADD_64   RIPPLEADD_64_SVA   rip64_sva(.clk(clk));
bind FULLADDER_1BIT FULLADDER_1BIT_SVA fa1_sva   (.clk(clk));