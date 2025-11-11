// SVA checkers for four_bit_adder and full_adder
// Focused, concise, and bind-ready

// Checker for the 4-bit ripple-carry adder (uses internal carries and S bus)
module four_bit_adder_sva_chk (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] Sum,
  input  logic       Cout,

  // internal nets from four_bit_adder
  input  logic [3:0] S,
  input  logic       C1, C2, C3
);
  // Expected ripple-carry computation
  logic [3:0] p;       // propagate
  logic [3:0] g;       // generate
  logic [4:0] c;       // carries
  logic [3:0] exp_sum;
  logic       exp_cout;
  logic [4:0] exp_5;

  always_comb begin
    p = A ^ B;
    g = A & B;
    c[0] = Cin;
    for (int i=0; i<4; i++) c[i+1] = g[i] | (p[i] & c[i]);
    exp_sum  = p ^ c[3:0];
    exp_cout = c[4];
    exp_5    = {exp_cout, exp_sum};

    // Functional equivalence (5-bit result)
    assert (#0 {Cout, Sum} == exp_5)
      else $error("4b-adder mismatch: A=%0h B=%0h Cin=%0b -> got {%0b,%0h} exp {%0b,%0h}",
                  A,B,Cin,Cout,Sum,exp_cout,exp_sum);

    // Internal carry chain checks
    assert (#0 C1 == c[1]) else $error("C1 incorrect");
    assert (#0 C2 == c[2]) else $error("C2 incorrect");
    assert (#0 C3 == c[3]) else $error("C3 incorrect");

    // Output connectivity to internal S bus
    assert (#0 Sum == S) else $error("Sum != internal S");

    // Outputs must be known when inputs are known
    if (!$isunknown({A,B,Cin})) begin
      assert (#0 !$isunknown({Sum,Cout})) else $error("X/Z on outputs with known inputs");
    end

    // Minimal but meaningful coverage
    cover (A==4'h0 && B==4'h0 && Cin==1'b0 && Sum==4'h0 && Cout==1'b0); // zero + zero
    cover (A==4'hF && B==4'hF && Cin==1'b1 && Sum==4'hF && Cout==1'b1); // max + carry
    cover ((A^B)==4'hF && Cin==1'b1 && Sum==4'h0 && Cout==1'b1);        // full propagate
    cover ((A&B)!=4'h0 && (A^B)==4'h0 && Cin==1'b0 && Cout==1'b1);      // pure generate
  end
endmodule


// Checker for a single full_adder truth table and equations
module full_adder_sva_chk (
  input  logic A,
  input  logic B,
  input  logic Cin,
  input  logic S,
  input  logic Cout
);
  logic exp_s, exp_co;
  always_comb begin
    exp_s  = A ^ B ^ Cin;
    exp_co = (A & B) | ((A ^ B) & Cin);

    assert (#0 S   == exp_s)
      else $error("FA S mismatch: A=%0b B=%0b Cin=%0b got S=%0b exp=%0b",A,B,Cin,S,exp_s);
    assert (#0 Cout== exp_co)
      else $error("FA Cout mismatch: A=%0b B=%0b Cin=%0b got C=%0b exp=%0b",A,B,Cin,Cout,exp_co);

    if (!$isunknown({A,B,Cin})) begin
      assert (#0 !$isunknown({S,Cout})) else $error("FA X/Z on outputs with known inputs");
    end
  end

  // Cover all 8 input combinations succinctly
  generate
    for (genvar i=0; i<8; i++) begin : COV
      // Expected outputs folded in to avoid covering wrong behavior
      localparam logic ia = i[2];
      localparam logic ib = i[1];
      localparam logic ic = i[0];
      localparam logic is = ia ^ ib ^ ic;
      localparam logic io = (ia & ib) | ((ia ^ ib) & ic);
      always_comb cover ({A,B,Cin,S,Cout} == {ia,ib,ic,is,io});
    end
  endgenerate
endmodule


// Bind into DUTs
bind four_bit_adder four_bit_adder_sva_chk u_four_bit_adder_sva_chk (
  .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout),
  .S(S), .C1(C1), .C2(C2), .C3(C3)
);

bind full_adder    full_adder_sva_chk    u_full_adder_sva_chk (
  .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout)
);