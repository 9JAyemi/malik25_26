// SVA for mux21_SIZE4_3 and its leaf cell MUX2_X1. Bind these into the DUT.

module mux21_SIZE4_3_sva #(parameter WIDTH=4)
(
  input  logic [WIDTH-1:0] IN0,
  input  logic [WIDTH-1:0] IN1,
  input  logic             CTRL,
  input  logic [WIDTH-1:0] OUT1
);
  // Functional correctness and X-prop hygiene
  always_comb begin
    assert (OUT1 === (CTRL ? IN1 : IN0))
      else $error("mux21_SIZE4_3: OUT1 != (CTRL ? IN1 : IN0)");
    assert (!$isunknown(CTRL))
      else $error("mux21_SIZE4_3: CTRL is X/Z");
    if (!$isunknown({CTRL,IN0,IN1}))
      assert (!$isunknown(OUT1))
        else $error("mux21_SIZE4_3: OUT1 has X/Z with known inputs");
  end

  // Minimal, meaningful coverage
  cover property (@(posedge CTRL) 1);
  cover property (@(negedge CTRL) 1);

  genvar i;
  generate for (i=0; i<WIDTH; i++) begin : g_out_cov
    cover property (@(posedge OUT1[i]) 1);
    cover property (@(negedge OUT1[i]) 1);
  end endgenerate
endmodule


module mux2_x1_sva (
  input logic A, B, S, Z
);
  // Leaf cell correctness and X-prop hygiene
  always_comb begin
    assert (Z === (S ? B : A))
      else $error("MUX2_X1: Z != (S ? B : A)");
    assert (!$isunknown(S))
      else $error("MUX2_X1: S is X/Z");
    if (!$isunknown({A,B,S}))
      assert (!$isunknown(Z))
        else $error("MUX2_X1: Z has X/Z with known inputs");
  end

  // Coverage
  cover property (@(posedge S) 1);
  cover property (@(negedge S) 1);
  cover property (@(posedge Z) 1);
  cover property (@(negedge Z) 1);
endmodule


// Bind into DUT
bind mux21_SIZE4_3 mux21_SIZE4_3_sva sva_mux21(.IN0(IN0), .IN1(IN1), .CTRL(CTRL), .OUT1(OUT1));
bind MUX2_X1       mux2_x1_sva       sva_cell (.A(A),     .B(B),     .S(S),     .Z(Z));