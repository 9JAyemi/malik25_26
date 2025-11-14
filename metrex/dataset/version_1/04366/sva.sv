// SVA checker for and4. Bind this to the DUT to verify functionality and collect coverage.
module and4_sva (
  input logic A, B, C, D,
  input logic W, Y,
  input logic X
);
  // Functional correctness (4-state exact)
  always_comb begin
    assert (W === (A & B)) else $error("and4: W != A&B A=%b B=%b W=%b", A,B,W);
    assert (Y === (C & D)) else $error("and4: Y != C&D C=%b D=%b Y=%b", C,D,Y);
    assert (X === (W & Y)) else $error("and4: X != W&Y W=%b Y=%b X=%b", W,Y,X);
    assert (X === (A & B & C & D)) else $error("and4: X != A&B&C&D A=%b B=%b C=%b D=%b X=%b", A,B,C,D,X);
    if (!$isunknown({A,B,C,D})) assert (!$isunknown(X)) else $error("and4: X is X/Z while inputs known A=%b B=%b C=%b D=%b X=%b", A,B,C,D,X);
  end

  // Output toggle coverage
  cover property (@(posedge X) 1);
  cover property (@(negedge X) 1);

  // Input combination coverage (all 16 2-state combos)
  generate
    genvar gi;
    for (gi=0; gi<16; gi++) begin: comb_cov
      localparam logic [3:0] COMBO = gi[3:0];
      cover property (@(posedge A or negedge A or
                        posedge B or negedge B or
                        posedge C or negedge C or
                        posedge D or negedge D)
                      (! $isunknown({A,B,C,D})) && ({A,B,C,D} == COMBO));
    end
  endgenerate

  // X-propagation coverage for single X with other inputs =1
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
                  (B===1 && C===1 && D===1 && A===1'bx) && (W===1'bx || X===1'bx));
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
                  (A===1 && C===1 && D===1 && B===1'bx) && (W===1'bx || X===1'bx));
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
                  (A===1 && B===1 && D===1 && C===1'bx) && (Y===1'bx || X===1'bx));
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
                  (A===1 && B===1 && C===1 && D===1'bx) && (Y===1'bx || X===1'bx));
endmodule

// Bind into all and4 instances (gives access to internal W,Y)
bind and4 and4_sva u_and4_sva (.A(A), .B(B), .C(C), .D(D), .W(W), .Y(Y), .X(X));