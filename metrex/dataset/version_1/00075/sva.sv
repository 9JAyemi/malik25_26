// SVA checkers and binds for the given design

// -------------- sky130_fd_sc_lp__inv_2 -----------------
module sva_inv_2 (input logic A, Y);
  // Functional correctness
  always_comb assert (Y === ~A)
    else $error("inv_2: Y must equal ~A");

  // X-propagation guard
  always_comb if (!$isunknown(A)) assert (!$isunknown(Y))
    else $error("inv_2: Y is X/Z while A is known");

  // Minimal toggle coverage
  cover property (@(posedge A) (Y==1'b0));
  cover property (@(negedge A) (Y==1'b1));
endmodule

bind sky130_fd_sc_lp__inv_2 sva_inv_2 inv2_sva_i (.A(A), .Y(Y));


// -------------- sky130_fd_sc_lp__nand2_1 -----------------
module sva_nand2_1 (input logic A1, A2, B1, X);
  // Functional correctness (original and simplified forms equivalent)
  always_comb assert (X === ((~A1 & ~A2) | ~B1))
    else $error("nand2_1: X must equal (~A1 & ~A2) | ~B1");
  // Known output when inputs known
  always_comb if (!$isunknown({A1,A2,B1})) assert (!$isunknown(X))
    else $error("nand2_1: X is X/Z while inputs are known");

  // Output 0/1 coverage on any input edge
  cover property (@(posedge A1 or negedge A1 or
                    posedge A2 or negedge A2 or
                    posedge B1 or negedge B1) (X==1'b0));
  cover property (@(posedge A1 or negedge A1 or
                    posedge A2 or negedge A2 or
                    posedge B1 or negedge B1) (X==1'b1));
endmodule

bind sky130_fd_sc_lp__nand2_1 sva_nand2_1 nand2_1_sva_i (.A1(A1), .A2(A2), .B1(B1), .X(X));


// -------------- sky130_fd_sc_lp__nand2_4 -----------------
module sva_nand2_4 (input logic A1, A2, B1, X,
                    input logic A3, A4); // internal nets bound by name
  // Structure/local correctness
  always_comb assert (A3 === ~A1)
    else $error("nand2_4: A3 must equal ~A1 (inv U1)");
  always_comb assert (A4 === ~A2)
    else $error("nand2_4: A4 must equal ~A2 (inv U2)");

  // End-to-end functional correctness
  always_comb assert (X === ((A1 & A2) | ~B1))
    else $error("nand2_4: X must equal (A1 & A2) | ~B1");

  // Known output when inputs known
  always_comb if (!$isunknown({A1,A2,B1})) assert (!$isunknown(X))
    else $error("nand2_4: X is X/Z while inputs are known");

  // Output 0/1 coverage on any input edge
  cover property (@(posedge A1 or negedge A1 or
                    posedge A2 or negedge A2 or
                    posedge B1 or negedge B1) (X==1'b0));
  cover property (@(posedge A1 or negedge A1 or
                    posedge A2 or negedge A2 or
                    posedge B1 or negedge B1) (X==1'b1));
endmodule

bind sky130_fd_sc_lp__nand2_4 sva_nand2_4 nand2_4_sva_i
  (.A1(A1), .A2(A2), .B1(B1), .X(X), .A3(A3), .A4(A4));


// -------------- sky130_fd_sc_lp__o41a_m -----------------
module sva_o41a_m (input logic A1, A2, A3, A4, B1, X,
                   input logic X_tmp);
  // Composition and function correctness
  always_comb assert (X === ~X_tmp)
    else $error("o41a_m: X must equal ~X_tmp");
  always_comb assert (X === ((~A1 | ~A2) & B1))
    else $error("o41a_m: X must equal (~A1 | ~A2) & B1");

  // Independence from unused inputs A3/A4
  always @(A3 or A4) assert ($stable(X))
    else $error("o41a_m: X must not depend on A3/A4");

  // Known output when used inputs known
  always_comb if (!$isunknown({A1,A2,B1})) assert (!$isunknown(X))
    else $error("o41a_m: X is X/Z while used inputs are known");

  // Output 0/1 coverage on any used input edge
  cover property (@(posedge A1 or negedge A1 or
                    posedge A2 or negedge A2 or
                    posedge B1 or negedge B1) (X==1'b0));
  cover property (@(posedge A1 or negedge A1 or
                    posedge A2 or negedge A2 or
                    posedge B1 or negedge B1) (X==1'b1));
endmodule

bind sky130_fd_sc_lp__o41a_m sva_o41a_m o41a_sva_i
  (.A1(A1), .A2(A2), .A3(A3), .A4(A4), .B1(B1), .X(X), .X_tmp(X_tmp));