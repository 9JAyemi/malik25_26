// SVA for mux_4to1
// Bind this module to mux_4to1 and drive clk from your TB.

module mux_4to1_sva (
  input logic clk,
  // DUT ports
  input logic A, B, C, D, S0, S1, Y,
  // internal DUT nets (bound)
  input logic sel1, sel2
);
  default clocking cb @(posedge clk); endclocking

  // X-safe functional equivalence (canonical 4:1 behavior as implemented)
  assert property (Y === (S1 ? (S0 ? D : B) : (S0 ? A : C)))
    else $error("mux_4to1: functional mismatch");

  // Check internal select stages
  assert property (sel1 === ((S1 == 1'b0) ? S0 : ~S0))
    else $error("mux_4to1: sel1 mismatch");
  assert property (sel2 === ((S1 == 1'b0) ? A  : B))
    else $error("mux_4to1: sel2 mismatch");

  // Deterministic mapping when selects are known
  assert property ((!$isunknown({S1,S0})) |->
                   (S1 ? (S0 ? (Y===D) : (Y===B))
                       : (S0 ? (Y===A) : (Y===C))))
    else $error("mux_4to1: mapping mismatch for known selects");

  // No X on Y when selects and selected input are known
  assert property ((!$isunknown({S1,S0})) &&
                   (S1 ? (S0 ? !$isunknown(D) : !$isunknown(B))
                       : (S0 ? !$isunknown(A) : !$isunknown(C)))
                   |-> !$isunknown(Y))
    else $error("mux_4to1: unexpected X on Y");

  // Gating: unselected inputs do not affect Y (selectors and selected input stable)
  assert property ((S1==1'b0 && S0==1'b0 && $stable(C) && $changed({A,B})) |-> $stable(Y))
    else $error("mux_4to1: Y changed due to unselected A/B when selecting C");
  assert property ((S1==1'b0 && S0==1'b1 && $stable(A) && $changed({B,C,D})) |-> $stable(Y))
    else $error("mux_4to1: Y changed due to unselected B/C/D when selecting A");
  assert property ((S1==1'b1 && S0==1'b0 && $stable(B) && $changed({A,C,D})) |-> $stable(Y))
    else $error("mux_4to1: Y changed due to unselected A/C/D when selecting B");
  assert property ((S1==1'b1 && S0==1'b1 && $stable(D) && $changed({A,B,C})) |-> $stable(Y))
    else $error("mux_4to1: Y changed due to unselected A/B/C when selecting D");

  // Basic functional coverage: each selection path hit
  cover property (S1==1'b0 && S0==1'b0 && Y===C);
  cover property (S1==1'b0 && S0==1'b1 && Y===A);
  cover property (S1==1'b1 && S0==1'b0 && Y===B);
  cover property (S1==1'b1 && S0==1'b1 && Y===D);

  // Pass-through coverage: selected data toggles and Y follows
  cover property (S1==1'b0 && S0==1'b0 ##1 $changed(C) && (Y===C));
  cover property (S1==1'b0 && S0==1'b1 ##1 $changed(A) && (Y===A));
  cover property (S1==1'b1 && S0==1'b0 ##1 $changed(B) && (Y===B));
  cover property (S1==1'b1 && S0==1'b1 ##1 $changed(D) && (Y===D));

endmodule

// Example bind (adjust clk name as appropriate):
// bind mux_4to1 mux_4to1_sva u_mux_4to1_sva (
//   .clk(tb_clk),
//   .A(A), .B(B), .C(C), .D(D), .S0(S0), .S1(S1), .Y(Y),
//   .sel1(sel1), .sel2(sel2)
// );