// SVA for D_FlipFlop
module D_FlipFlop_sva(input logic Q, D, CLK, RST);
  default clocking cb @(posedge CLK); endclocking

  // Async reset dominates immediately and while asserted
  assert property (@(posedge RST) Q == 1'b0);
  assert property (@(posedge CLK) RST |-> (Q == 1'b0));

  // Capture behavior on CLK when not in reset
  assert property (@cb disable iff (RST) Q == $past(D));

  // Basic functional coverage of 0->1 and 1->0 captures
  cover property (@cb disable iff (RST) $rose(D) ##1 (Q == 1));
  cover property (@cb disable iff (RST) $fell(D) ##1 (Q == 0));
endmodule

bind D_FlipFlop D_FlipFlop_sva dff_chk(.Q(Q), .D(D), .CLK(CLK), .RST(RST));


// SVA for full_adder (combinational intent)
module full_adder_sva(input logic A, B, C_in, S, C_out);
  // Sum must be correct
  assert property (@(*) S == (A ^ B ^ C_in));

  // Carry must be majority(A,B,Cin)
  assert property (@(*) C_out == ((A & B) | (A & C_in) | (B & C_in)));

  // Minimal coverage
  cover property (@(*) C_out == 1);
  cover property (@(*) (S == 1));
endmodule

bind full_adder full_adder_sva fa_chk(.A(A), .B(B), .C_in(C_in), .S(S), .C_out(C_out));


// SVA for ripple_adder
module ripple_adder_sva(
  input  logic [3:0] A, B,
  input  logic       Cin,
  input  logic [3:0] Sum,
  input  logic       Cout,
  // tap internal chain
  input  logic [3:0] s,
  input  logic [3:0] c
);
  function automatic logic maj3(input logic a,b,c); return (a&b)|(a&c)|(b&c); endfunction

  // End-to-end correctness
  assert property (@(*) {Cout,Sum} == (A + B + Cin));

  // Bitwise stage checks
  // bit 0
  assert property (@(*) s[0] == (A[0] ^ B[0] ^ Cin));
  assert property (@(*) c[0] == maj3(A[0], B[0], Cin));
  // bit 1..2 internal carries
  assert property (@(*) s[1] == (A[1] ^ B[1] ^ c[0]));
  assert property (@(*) c[1] == maj3(A[1], B[1], c[0]));
  assert property (@(*) s[2] == (A[2] ^ B[2] ^ c[1]));
  assert property (@(*) c[2] == maj3(A[2], B[2], c[1]));
  // bit 3 to external Cout
  assert property (@(*) s[3] == (A[3] ^ B[3] ^ c[2]));
  assert property (@(*) Cout == maj3(A[3], B[3], c[2]));

  // Key coverage: overflow and extremes
  cover property (@(*) Cout == 1);
  cover property (@(*) Sum == 4'h0);
  cover property (@(*) Sum == 4'hF);
endmodule

bind ripple_adder ripple_adder_sva ra_chk(
  .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout),
  .s(s), .c(c)
);