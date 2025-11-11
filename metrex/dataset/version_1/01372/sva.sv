// SVA checker for sky130_fd_sc_ls__a211o
// Function: X = (A1 & A2) | B1 | C1
module sky130_fd_sc_ls__a211o_sva #(
  parameter bit USE_CLK = 0
) (
  input logic A1, A2, B1, C1,
  input logic X,
  input logic VPWR, VGND, VPB, VNB,
  input logic clk  // optional if USE_CLK=1
);

  // Power pin sanity
  initial begin
    assert (VPWR === 1'b1 && VPB === 1'b1 && VGND === 1'b0 && VNB === 1'b0)
      else $error("a211o: bad power pins VPWR=%b VPB=%b VGND=%b VNB=%b", VPWR,VPB,VGND,VNB);
  end

  // Combinational immediate checks (race-safe via #0)
  always_comb begin
    // Output must be known and functionally correct when inputs are known
    if (!$isunknown({A1,A2,B1,C1})) begin
      assert #0 (X === ((A1 & A2) | B1 | C1))
        else $error("a211o func mismatch: X=%0b exp=%0b A1=%0b A2=%0b B1=%0b C1=%0b",
                    X, ((A1 & A2) | B1 | C1), A1, A2, B1, C1);
      assert #0 (!$isunknown(X))
        else $error("a211o: X unknown with known inputs A1=%b A2=%b B1=%b C1=%b", A1,A2,B1,C1);
    end

    // Dominance: any known 1 on B1 or C1 forces X=1 irrespective of others
    if (!$isunknown(B1) && B1) assert #0 (X === 1'b1)
      else $error("a211o: B1=1 but X!=1");
    if (!$isunknown(C1) && C1) assert #0 (X === 1'b1)
      else $error("a211o: C1=1 but X!=1");

    // OFF-case: with B1=0,C1=0 and any 0 on A1 or A2, X must be 0
    if (!$isunknown({A1,A2,B1,C1}) && !B1 && !C1 && (!A1 || !A2))
      assert #0 (X === 1'b0)
        else $error("a211o: expected X=0 when B1=C1=0 and (A1=0 or A2=0)");
  end

  // Optional concurrent SVA (use when a clock is available)
  generate if (USE_CLK) begin : g_clk
    default clocking cb @(posedge clk); endclocking

    // Functional equivalence under known inputs
    assert property (!$isunknown({A1,A2,B1,C1}) |-> X == ((A1 & A2) | B1 | C1));

    // Immediate dominance on rising B1/C1 (##0 to sample after update)
    assert property (B1 |-> ##0 X);
    assert property (C1 |-> ##0 X);

    // Coverage: all ways to assert X and the single OFF condition
    cover property (B1 ##0 X);
    cover property (C1 ##0 X);
    cover property ((A1 && A2 && !B1 && !C1) ##0 X);
    cover property ((!A1 || !A2) && !B1 && !C1 ##0 !X);

    // Coverage: observe both X edges
    cover property (!$past(X) && X);
    cover property ($past(X) && !X);
  end endgenerate

endmodule

// Bind into the DUT (no clock available by default; set USE_CLK=1 and pass a clock if desired)
bind sky130_fd_sc_ls__a211o sky130_fd_sc_ls__a211o_sva #(.USE_CLK(0)) u_a211o_sva (
  .A1(A1), .A2(A2), .B1(B1), .C1(C1),
  .X(X), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
  .clk(1'b0)
);