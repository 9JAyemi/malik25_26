// SVA for sky130_fd_sc_ms__nor4bb
// Function: Y = (~(A | B)) & C_N & D_N = (~A & ~B & C_N & D_N)

module sky130_fd_sc_ms__nor4bb_sva
(
  input logic A, B, C_N, D_N,
  input logic Y,
  input logic nor0_out,
  input logic and0_out_Y,
  input logic VPWR, VGND, VPB, VNB
);

  // Consider checks valid only when rails are good
  wire powered = (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);

  // Functional equivalence at output
  property p_func;
    @(posedge A or negedge A or
      posedge B or negedge B or
      posedge C_N or negedge C_N or
      posedge D_N or negedge D_N)
    disable iff (!powered)
      Y === ((~(A | B)) & C_N & D_N);
  endproperty
  assert property (p_func);

  // Internal net checks (structure)
  property p_nor0_out;
    @(posedge A or negedge A or posedge B or negedge B)
    disable iff (!powered)
      nor0_out === ~(A | B);
  endproperty
  assert property (p_nor0_out);

  property p_and0_out;
    @(posedge nor0_out or negedge nor0_out or
      posedge C_N or negedge C_N or
      posedge D_N or negedge D_N)
    disable iff (!powered)
      and0_out_Y === (nor0_out & C_N & D_N);
  endproperty
  assert property (p_and0_out);

  property p_buf;
    @(posedge and0_out_Y or negedge and0_out_Y)
    disable iff (!powered)
      Y === and0_out_Y;
  endproperty
  assert property (p_buf);

  // If all inputs are known, output must be known
  property p_known_out_when_inputs_known;
    @(posedge A or negedge A or
      posedge B or negedge B or
      posedge C_N or negedge C_N or
      posedge D_N or negedge D_N)
    disable iff (!powered)
      (!$isunknown(A) && !$isunknown(B) && !$isunknown(C_N) && !$isunknown(D_N))
      |-> !$isunknown(Y);
  endproperty
  assert property (p_known_out_when_inputs_known);

  // Compact functional coverage
  // 1) Only minterm that makes Y=1
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N or posedge D_N or negedge D_N)
                  powered && A==0 && B==0 && C_N==1 && D_N==1 && Y==1);

  // 2) Y low due to each controlling-zero path
  cover property (@(posedge C_N or negedge C_N) powered && C_N==0 && Y==0);
  cover property (@(posedge D_N or negedge D_N) powered && D_N==0 && Y==0);

  // 3) Y low due to A/B high when enables are 1
  cover property (@(posedge A or negedge A) powered && C_N==1 && D_N==1 && A==1 && Y==0);
  cover property (@(posedge B or negedge B) powered && C_N==1 && D_N==1 && B==1 && Y==0);

endmodule

// Bind into the DUT (allows access to internals)
bind sky130_fd_sc_ms__nor4bb sky130_fd_sc_ms__nor4bb_sva
(
  .A(A), .B(B), .C_N(C_N), .D_N(D_N),
  .Y(Y),
  .nor0_out(nor0_out),
  .and0_out_Y(and0_out_Y),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);