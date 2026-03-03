// SVA checker for four_bit_adder. Bind this to the DUT and connect a sampling clock.
module four_bit_adder_sva (
  input  logic        clk,
  input  logic [3:0]  A, B, S,
  input  logic        Cin, Cout,
  input  logic [2:0]  carry // DUT internal carries [2:0]
);

  // Combinational equivalence and bit-slice checks (immediate assertions)
  always_comb begin
    if (!$isunknown({A,B,Cin})) begin
      assert ({Cout,S} == A + B + Cin)
        else $error("Adder mismatch: A=%0h B=%0h Cin=%0b -> S=%0h Cout=%0b", A,B,Cin,S,Cout);

      assert ({carry[0], S[0]} == (A[0] + B[0] + Cin));
      assert ({carry[1], S[1]} == (A[1] + B[1] + carry[0]));
      assert ({carry[2], S[2]} == (A[2] + B[2] + carry[1]));
      assert ({Cout,     S[3]} == (A[3] + B[3] + carry[2]));

      assert (S[0] == (A[0] ^ B[0] ^ Cin));
      assert (carry[0] == ((A[0] & B[0]) | (B[0] & Cin) | (A[0] & Cin)));

      assert (S[1] == (A[1] ^ B[1] ^ carry[0]));
      assert (carry[1] == ((A[1] & B[1]) | (B[1] & carry[0]) | (A[1] & carry[0])));

      assert (S[2] == (A[2] ^ B[2] ^ carry[1]));
      assert (carry[2] == ((A[2] & B[2]) | (B[2] & carry[1]) | (A[2] & carry[1])));

      assert (S[3] == (A[3] ^ B[3] ^ carry[2]));
      assert (Cout   == ((A[3] & B[3]) | (B[3] & carry[2]) | (A[3] & carry[2])));

      assert (!$isunknown({S,Cout,carry}));
    end
  end

  // Concurrent SVA (use any convenient sampling clock)
  default clocking cb @ (posedge clk); endclocking

  // Purely combinational: if inputs stable across a sample, outputs are stable
  assert property ($stable({A,B,Cin}) |-> $stable({S,Cout}));

  // Key functional scenarios
  cover property (A==4'h0 && B==4'h0 && Cin==1'b0 && S==4'h0 && Cout==1'b0); // zero
  cover property ((A^B)==4'hF && Cin && (S==4'h0) && Cout);                  // full propagate
  cover property (A==4'hF && B==4'hF && Cin && S==4'hF && Cout);             // max + max + 1 overflow

  // Per-stage carry behaviors: generate, propagate, kill
  logic [3:0] ci, co;
  assign ci = {carry[2], carry[1], carry[0], Cin};    // cin per stage [3:0]
  assign co = {Cout,     carry[2], carry[1], carry[0]}; // cout per stage [3:0]

  genvar i;
  generate
    for (i=0; i<4; i++) begin : per_stage_cov
      cover property ( (A[i] & B[i]) && co[i] );                 // generate: ab=1 -> cout=1
      cover property ( (A[i]^B[i]) &&  ci[i] &&  co[i] );        // propagate with cin=1
      cover property ( (A[i]^B[i]) && !ci[i] && !co[i] );        // propagate with cin=0
      cover property ( !(A[i]|B[i]) && ci[i] && !co[i] );        // kill: a=b=0 -> no cout
    end
  endgenerate

endmodule

// Example bind (connect clk to a TB clock or $global_clock if supported):
// bind four_bit_adder four_bit_adder_sva sva ( .clk(tb_clk), .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout), .carry(carry[2:0]) );