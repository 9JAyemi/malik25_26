// SVA checker for sky130_fd_sc_lp__o221ai
// Concise, high-quality functional and X-prop checks with useful coverage.
module sky130_fd_sc_lp__o221ai_sva (
  input logic Y,
  input logic A1, A2, B1, B2, C1,
  input logic VPWR, VGND
);

  // Functional equivalence (4-state)
  a_func_eq: assert property ( Y === (A1 & A2 & B1 & B2 & C1 & VPWR & VGND) );

  // Necessary conditions
  a_y1_implies_all1: assert property ( (Y===1'b1)
                                       |-> (A1===1 && A2===1 && B1===1 && B2===1 && C1===1 && VPWR===1 && VGND===1) );
  a_any0_implies_y0: assert property ( ((A1===0)||(A2===0)||(B1===0)||(B2===0)||(C1===0)||(VPWR===0)||(VGND===0))
                                       |-> (Y===1'b0) );

  // No spurious output changes
  a_no_spurious_y_change: assert property ( $changed(Y)
                                            |-> ($changed(A1)||$changed(A2)||$changed(B1)||$changed(B2)||$changed(C1)||$changed(VPWR)||$changed(VGND)) );

  // X-propagation for AND: if no input is 0 and at least one is X/Z, Y must be X/Z
  a_xprop_and: assert property (
    !(A1===0 || A2===0 || B1===0 || B2===0 || C1===0 || VPWR===0 || VGND===0)
    && ($isunknown(A1)||$isunknown(A2)||$isunknown(B1)||$isunknown(B2)||$isunknown(C1)||$isunknown(VPWR)||$isunknown(VGND))
    |-> $isunknown(Y)
  );

  // Edge-accurate toggle causality (concise OR across inputs)
  a_rise_last_one: assert property (
      ( $rose(A1) && A2===1 && B1===1 && B2===1 && C1===1 && VPWR===1 && VGND===1 )
   || ( $rose(A2) && A1===1 && B1===1 && B2===1 && C1===1 && VPWR===1 && VGND===1 )
   || ( $rose(B1) && A1===1 && A2===1 && B2===1 && C1===1 && VPWR===1 && VGND===1 )
   || ( $rose(B2) && A1===1 && A2===1 && B1===1 && C1===1 && VPWR===1 && VGND===1 )
   || ( $rose(C1) && A1===1 && A2===1 && B1===1 && B2===1 && VPWR===1 && VGND===1 )
   || ( $rose(VPWR) && A1===1 && A2===1 && B1===1 && B2===1 && C1===1 && VGND===1 )
   || ( $rose(VGND) && A1===1 && A2===1 && B1===1 && B2===1 && C1===1 && VPWR===1 )
    |-> $rose(Y)
  );

  a_fall_any_one: assert property (
      ( $fell(A1) && A2===1 && B1===1 && B2===1 && C1===1 && VPWR===1 && VGND===1 )
   || ( $fell(A2) && A1===1 && B1===1 && B2===1 && C1===1 && VPWR===1 && VGND===1 )
   || ( $fell(B1) && A1===1 && A2===1 && B2===1 && C1===1 && VPWR===1 && VGND===1 )
   || ( $fell(B2) && A1===1 && A2===1 && B1===1 && C1===1 && VPWR===1 && VGND===1 )
   || ( $fell(C1) && A1===1 && A2===1 && B1===1 && B2===1 && VPWR===1 && VGND===1 )
   || ( $fell(VPWR) && A1===1 && A2===1 && B1===1 && B2===1 && C1===1 && VGND===1 )
   || ( $fell(VGND) && A1===1 && A2===1 && B1===1 && B2===1 && C1===1 && VPWR===1 )
    |-> $fell(Y)
  );

  // Output edge sanity
  a_roseY_all1_now:  assert property ( $rose(Y) |-> (A1===1 && A2===1 && B1===1 && B2===1 && C1===1 && VPWR===1 && VGND===1) );
  a_fellY_some0_now: assert property ( $fell(Y) |-> !(A1===1 && A2===1 && B1===1 && B2===1 && C1===1 && VPWR===1 && VGND===1) );

  // Coverage
  c_y0:   cover property ( Y===1'b0 );
  c_y1:   cover property ( Y===1'b1 );
  c_rise: cover property ( $rose(Y) );
  c_fall: cover property ( $fell(Y) );
  c_all1: cover property ( (A1===1 && A2===1 && B1===1 && B2===1 && C1===1 && VPWR===1 && VGND===1) && (Y===1) );

endmodule

// Bind into the DUT
bind sky130_fd_sc_lp__o221ai sky130_fd_sc_lp__o221ai_sva i_sky130_fd_sc_lp__o221ai_sva (.*);