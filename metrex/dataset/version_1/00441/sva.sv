// SVA checkers and binds for FourBitFA and FA

// 1-bit full-adder checker (binds to every FA instance)
module sva_FA (input logic A, B, Cin, Sum, Cout);
  // Functional equivalence
  assert property (@(*) Sum  == (A ^ B) ^ Cin);
  assert property (@(*) Cout == ((A & B) | (A & Cin) | (B & Cin)));

  // Clean outputs if inputs are clean
  assert property (@(*) !($isunknown({A,B,Cin})) |-> !($isunknown({Sum,Cout})));

  // Basic coverage of generate/kill/propagate
  cover property (@(*) (A & B));                 // generate
  cover property (@(*) (~A & ~B));               // kill
  cover property (@(*) ((A ^ B) && !Cin));       // propagate with Cin=0
  cover property (@(*) ((A ^ B) &&  Cin));       // propagate with Cin=1
endmodule

bind FA sva_FA SVA_FA_I (.*);

// 4-bit ripple-carry adder checker (binds to FourBitFA; uses internal FTemp)
module sva_FourBitFA #(parameter int SIZE = 4)
(
  input  logic [SIZE-1:0] FA, FB,
  input  logic            FCin,
  input  logic [SIZE-1:0] FTemp,
  input  logic [SIZE-1:0] FSum,
  input  logic            FCout
);
  // Sanity: this DUT is hard-wired for 4 bits
  initial assert (SIZE == 4) else $error("FourBitFA: SIZE must be 4, got %0d", SIZE);

  // Whole-adder arithmetic equivalence
  assert property (@(*) {FCout, FSum} == ({1'b0, FA} + {1'b0, FB} + FCin));

  // Per-bit full-adder equivalence and cleanliness, plus coverage
  genvar i;
  for (i = 0; i < SIZE; i++) begin : GEN_BIT
    wire cin_i  = (i == 0)       ? FCin  : FTemp[i-1];
    wire cout_i = (i == SIZE-1)  ? FCout : FTemp[i];

    // Bit-slice sum and carry equations
    assert property (@(*) FSum[i]  == (FA[i] ^ FB[i]) ^ cin_i);
    assert property (@(*) cout_i   == ((FA[i] & FB[i]) | (FA[i] & cin_i) | (FB[i] & cin_i)));

    // Clean outputs if inputs are clean
    assert property (@(*) !($isunknown({FA[i],FB[i],cin_i})) |-> !($isunknown({FSum[i],cout_i})));

    // Coverage for generate/kill/propagate at each bit
    cover property (@(*) (FA[i] & FB[i]));                 // generate
    cover property (@(*) (~FA[i] & ~FB[i]));               // kill
    cover property (@(*) ((FA[i] ^ FB[i]) && !cin_i));     // propagate, Cin=0
    cover property (@(*) ((FA[i] ^ FB[i]) &&  cin_i));     // propagate, Cin=1
  end

  // Top-level carry/no-carry and zero-sum scenarios
  cover property (@(*) FCout);
  cover property (@(*) (FSum == {SIZE{1'b0}} && !FCout));
endmodule

bind FourBitFA sva_FourBitFA #(.SIZE(SIZE)) SVA_FourBitFA_I (.*);