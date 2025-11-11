// SVA checker for sky130_fd_sc_lp__nand4
module sky130_fd_sc_lp__nand4_sva (
  input logic A, B, C, D,
  input logic Y,
  input logic nand0_out_Y,
  input logic VPWR, VGND, VPB, VNB
);
  // Sample on any relevant edge
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge D or negedge D or
    posedge Y or negedge Y
  ); endclocking

  // Functional correctness (when inputs are known)
  assert property (disable iff ($isunknown({A,B,C,D}))
                   Y === ~(A & B & C & D));

  // Output must be known when inputs are known
  assert property (disable iff ($isunknown({A,B,C,D}))
                   !$isunknown(Y));

  // Buffer consistency with internal nand output
  assert property (Y === nand0_out_Y);

  // Corner cases
  assert property ((A && B && C && D) |-> (Y == 1'b0));
  assert property (disable iff ($isunknown({A,B,C,D}))
                   ((!A) || (!B) || (!C) || (!D)) |-> (Y == 1'b1));

  // Power pins sanity (constant supplies)
  initial begin
    assert (VPWR === 1'b1);
    assert (VPB  === 1'b1);
    assert (VGND === 1'b0);
    assert (VNB  === 1'b0);
  end

  // Coverage: both output polarities
  cover property (disable iff ($isunknown({A,B,C,D})) Y == 1'b1);
  cover property (disable iff ($isunknown({A,B,C,D})) Y == 1'b0);

  // Coverage: corner vectors
  cover property (disable iff ($isunknown({A,B,C,D})) (A&&B&&C&&D) ##0 (Y==1'b0));
  cover property (disable iff ($isunknown({A,B,C,D})) ((!A)||(!B)||(!C)||(!D)) ##0 (Y==1'b1));

  // Coverage: all 16 input combinations (ignore X/Z)
  covergroup cg_inputs @(cb);
    option.per_instance = 1;
    cp_inputs: coverpoint {A,B,C,D} iff (! $isunknown({A,B,C,D})) {
      bins all[] = {[4'b0000:4'b1111]};
    }
  endgroup
  cg_inputs cg_inputs_i = new();

  // Coverage: both output edges observed
  cover property (@(posedge Y) 1);
  cover property (@(negedge Y) 1);
endmodule

// Bind the checker to the DUT
bind sky130_fd_sc_lp__nand4 sky130_fd_sc_lp__nand4_sva nand4_sva_i (
  .A(A), .B(B), .C(C), .D(D), .Y(Y),
  .nand0_out_Y(nand0_out_Y),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
)