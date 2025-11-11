// SVA for sky130_fd_sc_lp__a32o_* hierarchy
// Focus: functional correctness, power pins, X-propagation, concise coverage

package sky130_a32o_sva_pkg;
  function automatic logic exp_a21o (logic A1, logic A2, logic B1);
    return (A1 ^ (A2 & B1));
  endfunction

  function automatic logic exp_a31o (logic A1, logic A2, logic A3, logic B1, logic B2);
    logic s1a, s1b, s2a, s2b;
    s1a = exp_a21o(A1,A2,B1);
    s1b = exp_a21o(A3,B2,s1a);
    s2a = exp_a21o(A1,A2,B2);
    s2b = exp_a21o(A3,B1,s2a);
    return (s1b | s2b);
  endfunction

  function automatic logic power_ok (logic VPWR, logic VGND, logic VPB, logic VNB);
    return (VPWR===1'b1 && VGND===1'b0 && VPB===VPWR && VNB===VGND);
  endfunction
endpackage

// a21o checker
module sky130_a21o_sva (
  output X, input A1, input A2, input B1,
  input VPWR, input VGND, input VPB, input VNB
);
  import sky130_a32o_sva_pkg::*;
  event ev; always @(A1 or A2 or B1 or VPWR or VGND or VPB or VNB) -> ev;

  // Power-tie check (when rails are known)
  assert property (@(ev) (!$isunknown({VPWR,VGND,VPB,VNB})) |-> (VPB===VPWR && VNB===VGND));

  // Functional equivalence and X-propagation under good power and known inputs
  assert property (@(ev) disable iff (!power_ok(VPWR,VGND,VPB,VNB))
                    (!$isunknown({A1,A2,B1})) |-> (X === exp_a21o(A1,A2,B1)));
  assert property (@(ev) power_ok(VPWR,VGND,VPB,VNB) && !$isunknown({A1,A2,B1}) |-> !$isunknown(X));

  // Minimal coverage
  cover property (@(ev) power_ok(VPWR,VGND,VPB,VNB) && !$isunknown({A1,A2,B1}) && $rose(X));
  cover property (@(ev) power_ok(VPWR,VGND,VPB,VNB) && !$isunknown({A1,A2,B1}) && $fell(X));
endmodule

// or2 checker
module sky130_or2_sva (
  output X, input A1, input A2,
  input VPWR, input VGND, input VPB, input VNB
);
  import sky130_a32o_sva_pkg::*;
  event ev; always @(A1 or A2 or VPWR or VGND or VPB or VNB) -> ev;

  assert property (@(ev) (!$isunknown({VPWR,VGND,VPB,VNB})) |-> (VPB===VPWR && VNB===VGND));
  assert property (@(ev) disable iff (!power_ok(VPWR,VGND,VPB,VNB))
                    (!$isunknown({A1,A2})) |-> (X === (A1 | A2)));
  assert property (@(ev) power_ok(VPWR,VGND,VPB,VNB) && !$isunknown({A1,A2}) |-> !$isunknown(X));

  cover property (@(ev) power_ok(VPWR,VGND,VPB,VNB) && !$isunknown({A1,A2}) && $changed(X));
endmodule

// a31o checker (composed behavior of the hierarchy core)
module sky130_a31o_sva (
  output X, input A1, input A2, input A3, input B1, input B2,
  input VPWR, input VGND, input VPB, input VNB
);
  import sky130_a32o_sva_pkg::*;
  event ev; always @(A1 or A2 or A3 or B1 or B2 or VPWR or VGND or VPB or VNB) -> ev;

  assert property (@(ev) (!$isunknown({VPWR,VGND,VPB,VNB})) |-> (VPB===VPWR && VNB===VGND));
  assert property (@(ev) disable iff (!power_ok(VPWR,VGND,VPB,VNB))
                    (!$isunknown({A1,A2,A3,B1,B2})) |-> (X === exp_a31o(A1,A2,A3,B1,B2)));
  assert property (@(ev) power_ok(VPWR,VGND,VPB,VNB) && !$isunknown({A1,A2,A3,B1,B2}) |-> !$isunknown(X));

  // Useful corner checks to strengthen intent
  assert property (@(ev) disable iff (!power_ok(VPWR,VGND,VPB,VNB))
                    (B1==0 && B2==0 && !$isunknown({A3})) |-> (X===A3));
  assert property (@(ev) disable iff (!power_ok(VPWR,VGND,VPB,VNB))
                    (B1==1 && B2==1 && !$isunknown({A1,A2,A3})) |-> (X===(A3 ^ (A1 ^ A2))));

  // Minimal influence coverage: each input can toggle output at least once
  cover property (@(ev) power_ok(VPWR,VGND,VPB,VNB) && !$isunknown({A1,A2,A3,B1,B2})
                  && $changed(A1) && $changed(X));
  cover property (@(ev) power_ok(VPWR,VGND,VPB,VNB) && !$isunknown({A1,A2,A3,B1,B2})
                  && $changed(A2) && $changed(X));
  cover property (@(ev) power_ok(VPWR,VGND,VPB,VNB) && !$isunknown({A1,A2,A3,B1,B2})
                  && $changed(A3) && $changed(X));
  cover property (@(ev) power_ok(VPWR,VGND,VPB,VNB) && !$isunknown({A1,A2,A3,B1,B2})
                  && $changed(B1) && $changed(X));
  cover property (@(ev) power_ok(VPWR,VGND,VPB,VNB) && !$isunknown({A1,A2,A3,B1,B2})
                  && $changed(B2) && $changed(X));
endmodule

// a32o top-level checker (both _1 and _4 reduce to a31o composed function)
module sky130_a32o_top_sva (
  output X, input A1, input A2, input A3, input B1, input B2,
  input VPWR, input VGND, input VPB, input VNB
);
  import sky130_a32o_sva_pkg::*;
  event ev; always @(A1 or A2 or A3 or B1 or B2 or VPWR or VGND or VPB or VNB) -> ev;

  assert property (@(ev) (!$isunknown({VPWR,VGND,VPB,VNB})) |-> (VPB===VPWR && VNB===VGND));
  assert property (@(ev) disable iff (!power_ok(VPWR,VGND,VPB,VNB))
                    (!$isunknown({A1,A2,A3,B1,B2})) |-> (X === exp_a31o(A1,A2,A3,B1,B2)));
  assert property (@(ev) power_ok(VPWR,VGND,VPB,VNB) && !$isunknown({A1,A2,A3,B1,B2}) |-> !$isunknown(X));

  cover property (@(ev) power_ok(VPWR,VGND,VPB,VNB) && !$isunknown({A1,A2,A3,B1,B2}) && $rose(X));
  cover property (@(ev) power_ok(VPWR,VGND,VPB,VNB) && !$isunknown({A1,A2,A3,B1,B2}) && $fell(X));
endmodule

// Bindings
bind sky130_fd_sc_lp__a21o_1 sky130_a21o_sva a21o_sva_i (.*);
bind sky130_fd_sc_lp__or2_1  sky130_or2_sva  or2_sva_i  (.*);
bind sky130_fd_sc_lp__a31o_1 sky130_a31o_sva a31o_sva_i (.*);
bind sky130_fd_sc_lp__a32o_1 sky130_a32o_top_sva a32o1_sva_i (.*);
bind sky130_fd_sc_lp__a32o_4 sky130_a32o_top_sva a32o4_sva_i (.*);