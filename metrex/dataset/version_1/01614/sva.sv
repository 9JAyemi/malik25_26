// SVA for sky130_fd_sc_hs__o21a_*
// Spec: Y = (A1 | A2) & B1 when VPWR==1 and VGND==0

checker o21a_checker (input logic A1, A2, B1, VPWR, VGND, Y);
  function automatic bit pgood();
    return (VPWR === 1'b1) && (VGND === 1'b0);
  endfunction

  // Functional equivalence (power-aware)
  property p_func;
    @(posedge A1 or negedge A1 or
      posedge A2 or negedge A2 or
      posedge B1 or negedge B1 or
      posedge VPWR or negedge VPWR or
      posedge VGND or negedge VGND)
    disable iff (!pgood())
    Y === ((A1 | A2) & B1);
  endproperty
  assert property (p_func);

  // Known output when power is good
  property p_known;
    @(posedge A1 or negedge A1 or
      posedge A2 or negedge A2 or
      posedge B1 or negedge B1 or
      posedge VPWR or negedge VPWR or
      posedge VGND or negedge VGND)
    disable iff (!pgood())
    !$isunknown(Y);
  endproperty
  assert property (p_known);

  // Helpful local implications
  property p_b1_zero_forces_zero;
    @(posedge B1 or negedge B1)
    disable iff (!pgood())
    (!B1) |-> (Y == 1'b0);
  endproperty
  assert property (p_b1_zero_forces_zero);

  property p_b1_one_pass_or;
    @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
    disable iff (!pgood())
    (B1 && (A1 || A2)) |-> (Y == 1'b1);
  endproperty
  assert property (p_b1_one_pass_or);

  // Input-space coverage under power-good (8 combinations)
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  pgood() && (A1==0 && A2==0 && B1==0) && (Y==0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  pgood() && (A1==0 && A2==1 && B1==0) && (Y==0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  pgood() && (A1==1 && A2==0 && B1==0) && (Y==0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  pgood() && (A1==1 && A2==1 && B1==0) && (Y==0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  pgood() && (A1==0 && A2==0 && B1==1) && (Y==0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  pgood() && (A1==0 && A2==1 && B1==1) && (Y==1));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  pgood() && (A1==1 && A2==0 && B1==1) && (Y==1));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  pgood() && (A1==1 && A2==1 && B1==1) && (Y==1));

  // Output toggle coverage under power-good
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  pgood() && $rose(Y));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
                  pgood() && $fell(Y));
endchecker

// Bind to both drive-strength variants
bind sky130_fd_sc_hs__o21a_1 o21a_checker o21a_1_chk (.A1(A1), .A2(A2), .B1(B1), .VPWR(VPWR), .VGND(VGND), .Y(Y));
bind sky130_fd_sc_hs__o21a_2 o21a_checker o21a_2_chk (.A1(A1), .A2(A2), .B1(B1), .VPWR(VPWR), .VGND(VGND), .Y(Y));