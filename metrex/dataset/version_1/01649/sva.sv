// SVA checker for my_module
// - Concise, bindable, and focuses on functional correctness, X-prop, and key power behaviors.
// - Provide a free-running clk and an active-high rst_n when binding.

module my_module_sva #(
  parameter bit ENABLE_COV = 1
)(
  input logic clk,
  input logic rst_n,

  // DUT ports
  input logic X,
  input logic A1,
  input logic A2,
  input logic B1,
  input logic B2,
  input logic C1,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB,

  // DUT internals
  input logic and0_out,
  input logic and1_out,
  input logic or0_out_X,
  input logic pwrgood_pp0_out_X
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Pure functional equivalence (structural)
  assert property (and0_out           === (B1 & B2))
    else $error("and0_out != B1 & B2");
  assert property (and1_out           === (A1 & A2))
    else $error("and1_out != A1 & A2");
  assert property (or0_out_X          === (and1_out | and0_out | C1))
    else $error("or0_out_X != and1_out | and0_out | C1");
  assert property (pwrgood_pp0_out_X  === (or0_out_X & ~VPWR & VGND))
    else $error("pwrgood_pp0_out_X != or0_out_X & ~VPWR & VGND");
  assert property (X                  === pwrgood_pp0_out_X)
    else $error("X != pwrgood_pp0_out_X");

  // End-to-end logic equivalence (bypass internals too)
  assert property (or0_out_X === ((A1 & A2) | (B1 & B2) | C1))
    else $error("or0_out_X != (A1&A2)|(B1&B2)|C1");
  assert property (X === (((A1 & A2) | (B1 & B2) | C1) & ~VPWR & VGND))
    else $error("X != ((A1&A2)|(B1&B2)|C1) & ~VPWR & VGND");

  // No-X when inputs are known
  assert property (!$isunknown({A1,A2,B1,B2,C1,VPWR,VGND}))
    |-> (!$isunknown({and0_out,and1_out,or0_out_X,pwrgood_pp0_out_X,X}))
    else $error("Unknown on internal/output with known inputs");

  // Power-rail behavioral checks (derived from implemented pg function)
  assert property (VPWR==1'b1 |-> pwrgood_pp0_out_X==1'b0 && X==1'b0)
    else $error("When VPWR=1, pg path must hold low");
  assert property (VGND==1'b0 |-> pwrgood_pp0_out_X==1'b0 && X==1'b0)
    else $error("When VGND=0, pg path must hold low");
  assert property ((VPWR==1'b0 && VGND==1'b1) |-> (pwrgood_pp0_out_X==or0_out_X && X==or0_out_X))
    else $error("Pass condition (VPWR=0,VGND=1) not met");

  // VPB/VNB are present but unused in logic; ensure they never affect X (sanity via stability under VPB/VNB-only toggles)
  // If only VPB/VNB change, X must remain stable.
  assert property ($stable({A1,A2,B1,B2,C1,VPWR,VGND}) && $changed({VPB,VNB}) |-> $stable(X))
    else $error("X changed due to VPB/VNB-only activity");

  // Coverage (concise, key scenarios)
  if (ENABLE_COV) begin
    // Rail modes
    cover property (VPWR==1'b0 && VGND==1'b1); // "pass" mode per implemented pg
    cover property (VPWR==1'b1 && VGND==1'b0); // blocks
    cover property (VPWR==1'b1 && VGND==1'b1); // blocks
    cover property (VPWR==1'b0 && VGND==1'b0); // blocks

    // Each input term independently drives X high under pass condition
    cover property ((VPWR==1'b0 && VGND==1'b1) && (A1 & A2) && !B1 && !B2 && !C1 && X);
    cover property ((VPWR==1'b0 && VGND==1'b1) && (B1 & B2) && !A1 && !A2 && !C1 && X);
    cover property ((VPWR==1'b0 && VGND==1'b1) && C1 && !(A1 & A2) && !(B1 & B2) && X);

    // Output toggles under pass condition
    cover property ((VPWR==1'b0 && VGND==1'b1) && $rose(X));
    cover property ((VPWR==1'b0 && VGND==1'b1) && $fell(X));
  end

endmodule

// Example bind (from testbench or a package):
// bind my_module my_module_sva sva (
//   .clk(tb_clk), .rst_n(tb_rst_n),
//   .X(X), .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1),
//   .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
//   .and0_out(and0_out), .and1_out(and1_out),
//   .or0_out_X(or0_out_X), .pwrgood_pp0_out_X(pwrgood_pp0_out_X)
// );