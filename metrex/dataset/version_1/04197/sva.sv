// SVA checkers and binds for three_input_or_gate and or_gate_3

module three_input_or_gate_sva (
  input logic A, B, C_N, X,
  input logic VPWR, VGND, VPB, VNB,
  input logic or_output
);
  wire rails_ok = (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);

  // Connectivity: X must mirror or_output with zero-delay
  assert property (@(posedge X or negedge X or posedge or_output or negedge or_output)
                   ##0 (X === or_output))
    else $error("X must equal or_output");

  // Output known when inputs known
  assert property (@(posedge A or negedge A or posedge B or negedge B or
                     posedge C_N or negedge C_N or posedge VPWR or negedge VPWR or
                     posedge VGND or negedge VGND or posedge VPB or negedge VPB or
                     posedge VNB or negedge VNB)
                   (!$isunknown({A,B,C_N,VPWR,VGND,VPB,VNB})) |-> ##0 (!$isunknown(X)))
    else $error("X unknown while inputs known");

  // Intended function under nominal rails: X == A | B | ~C_N
  assert property (@(posedge A or negedge A or posedge B or negedge B or
                     posedge C_N or negedge C_N or posedge VPWR or negedge VPWR or
                     posedge VGND or negedge VGND or posedge VPB or negedge VPB or
                     posedge VNB or negedge VNB)
                   rails_ok |-> ##0 (X === (A | B | ~C_N)))
    else $error("X != A|B|~C_N under nominal rails");

  // Minimal functional coverage under nominal rails
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N)
                  rails_ok && !A && !B && C_N ##0 (X===1'b0));       // X can be 0
  cover property (@(posedge A) rails_ok && !B && C_N ##0 (X===1'b1)); // A alone drives X
  cover property (@(posedge B) rails_ok && !A && C_N ##0 (X===1'b1)); // B alone drives X
  cover property (@(negedge C_N) rails_ok && !A && !B ##0 (X===1'b1)); // ~C_N alone drives X
endmodule


module or_gate_3_sva (
  input logic A, B, C_N, X,
  input logic VPWR, VGND, VPB, VNB
);
  // Implementation equation must hold combinationally
  assert property (@(posedge A or negedge A or posedge B or negedge B or
                     posedge C_N or negedge C_N or posedge VPWR or negedge VPWR or
                     posedge VGND or negedge VGND or posedge VPB or negedge VPB or
                     posedge VNB or negedge VNB)
                   ##0 (X === (A | B | ~C_N | VPWR | VGND | VPB | VNB)))
    else $error("or_gate_3 equation mismatch");

  // Output known when inputs known
  assert property (@(posedge A or negedge A or posedge B or negedge B or
                     posedge C_N or negedge C_N or posedge VPWR or negedge VPWR or
                     posedge VGND or negedge VGND or posedge VPB or negedge VPB or
                     posedge VNB or negedge VNB)
                   (!$isunknown({A,B,C_N,VPWR,VGND,VPB,VNB})) |-> ##0 (!$isunknown(X)));

  // Rail sanity (optional but recommended)
  assert property (@(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or
                     posedge VPB or negedge VPB or posedge VNB or negedge VNB)
                   (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0))
    else $error("Power/Bias rails not at nominal values");
endmodule


bind three_input_or_gate three_input_or_gate_sva sva_top (.*);
bind or_gate_3          or_gate_3_sva          sva_leaf(.*);