// SVA checker for sky130_fd_sc_ls__a22o_2
// Binds to DUT and verifies functional correctness, power/bias, and provides coverage.

module sky130_fd_sc_ls__a22o_2_sva (
  input X,
  input A1, A2, B1, B2,
  input VPWR, VGND, VPB, VNB
);

  function automatic logic f(input logic a1,a2,b1,b2);
    f = (a1 & ~a2) | (~b1 & b2) | (~a1 & ~a2 & ~b1 & ~b2) | (a1 & a2 & b1 & b2);
  endfunction

  logic pwr_ok;
  always @* pwr_ok = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);

  // Rail/bias sanity
  assert property (@(VPWR or VGND or VPB or VNB) !$isunknown({VPWR,VGND,VPB,VNB}));
  assert property (@(VPWR or VGND or VPB or VNB)
                   (!$isunknown({VPWR,VGND}) && !$isunknown({VPB,VNB})) |-> ((VPB===VPWR) && (VNB===VGND)));

  // Functional equivalence (combinational, zero-delay) on any relevant change
  assert property (@(A1 or A2 or B1 or B2 or VPWR or VGND or VPB or VNB)
                   pwr_ok && !$isunknown({A1,A2,B1,B2}) |-> ##0 (X === f(A1,A2,B1,B2)));

  // Output must be 0/1 when powered
  assert property (@(A1 or A2 or B1 or B2 or VPWR or VGND or VPB or VNB) pwr_ok |-> !$isunknown(X));

  // Redundant immediate check (helps simulators without full SVA support on clockless properties)
  always @* if (pwr_ok && !$isunknown({A1,A2,B1,B2})) begin
    assert (X === f(A1,A2,B1,B2))
      else $error("a22o_2 func mismatch: A1=%b A2=%b B1=%b B2=%b X=%b exp=%b",
                  A1,A2,B1,B2,X,f(A1,A2,B1,B2));
  end

  // Coverage: all 16 input vectors under power-good, plus X values; also power up/down
  covergroup cg_inputs @(A1 or A2 or B1 or B2);
    cp_vec: coverpoint {A1,A2,B1,B2}
            iff (pwr_ok && !$isunknown({A1,A2,B1,B2})) { bins all[] = {[0:15]}; }
    cp_x:   coverpoint X iff (pwr_ok && !$isunknown(X)) { bins zero = {0}; bins one = {1}; }
    xcross: cross cp_vec, cp_x;
  endgroup
  initial begin automatic cg_inputs cg = new(); end

  cover property (@(VPWR or VGND or VPB or VNB) (!$past(pwr_ok) && pwr_ok)); // power-up
  cover property (@(VPWR or VGND or VPB or VNB) ( $past(pwr_ok) && !pwr_ok)); // power-down

endmodule

bind sky130_fd_sc_ls__a22o_2 sky130_fd_sc_ls__a22o_2_sva sva_i(.*);