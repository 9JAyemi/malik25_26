// SVA checker for full_adder_32
module full_adder_32_sva
(
  input  logic        clk,
  input  logic        rst_n,
  input  logic [31:0] A,
  input  logic [31:0] B,
  input  logic [31:0] Cin,   // DUT exposes 32-bit Cin; only Cin[0] is intended/used
  input  logic [31:0] Sum,
  input  logic        Cout
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // 33-bit reference adder using only Cin[0]
  function automatic logic [32:0] add33(input logic [31:0] a, b,
                                        input logic cin0);
    add33 = {1'b0, a} + {1'b0, b} + cin0;
  endfunction

  // Carry into bit k (k in [0..31])
  function automatic logic carry_in_at(input logic [31:0] a, b,
                                       input logic cin0, input int k);
    logic c;
    c = cin0;
    for (int j = 0; j < k; j++) begin
      c = (a[j] & b[j]) | (a[j] & c) | (b[j] & c);
    end
    return c;
  endfunction

  logic [32:0] exp;
  assign exp = add33(A, B, Cin[0]);

  // Functional equivalence: full 33-bit result matches reference model
  assert property ( {Cout, Sum} == exp );

  // Bit-level sum correctness against recomputed carry-in
  genvar i;
  generate
    for (i = 0; i < 32; i++) begin : g_bit_sum
      assert property ( Sum[i] == (A[i] ^ B[i] ^ carry_in_at(A, B, Cin[0], i)) );
    end
  endgenerate

  // MSB carry correctness using carry into bit 31
  assert property (
    Cout == ((A[31] & B[31]) |
             (A[31] & carry_in_at(A, B, Cin[0], 31)) |
             (B[31] & carry_in_at(A, B, Cin[0], 31)))
  );

  // Outputs known when inputs (A,B,Cin[0]) are known
  assert property ( !$isunknown({A, B, Cin[0]}) |-> !$isunknown({Sum, Cout}) );

  // Purely combinational: if all inputs stable, outputs stable next cycle
  assert property ( $stable({A, B, Cin}) |-> ##1 $stable({Sum, Cout}) );

  // Independence from Cin[31:1]: changing them alone must not change outputs
  assert property (
    $stable(A) && $stable(B) && $stable(Cin[0]) && $changed(Cin[31:1])
    |-> ##1 {Cout, Sum} == $past({Cout, Sum})
  );

  // Coverage: overflow, no-overflow, independence event, wrap with carry, all-ones sum
  cover property ( Cout == 1'b1 );
  cover property ( Cout == 1'b0 );
  cover property ( $stable(A) && $stable(B) && $stable(Cin[0]) && $changed(Cin[31:1]) );
  cover property ( exp[32] && (exp[31:0] == 32'h0000_0000) ); // wraparound with carry
  cover property ( (exp[31:0] == 32'hFFFF_FFFF) && !Cout );

endmodule

// Bind example (hook clk/rst_n from your TB or environment)
// bind full_adder_32 full_adder_32_sva u_fa32_sva(.clk(tb.clk), .rst_n(tb.rst_n),
//                                                 .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout));