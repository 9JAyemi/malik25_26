// SVA checker for multi_input_output
module multi_input_output_sva (
  input logic        clk,
  input logic [7:0]  A,B,C,D,E,F,G,H,
  input logic [7:0]  Y
);

  default clocking cb @(posedge clk); endclocking

  // Helpers
  let known_in     = !$isunknown({A,B,C,D,E,F,G,H});
  let known_all    = !$isunknown({A,B,C,D,E,F,G,H,Y});
  let y_exp        = (((A + B) - (C + D) + (E + F) - (G + H)) [7:0]);
  let ovAB         = ({1'b0,A}+{1'b0,B})[8];
  let ovCD         = ({1'b0,C}+{1'b0,D})[8];
  let ovEF         = ({1'b0,E}+{1'b0,F})[8];
  let ovGH         = ({1'b0,G}+{1'b0,H})[8];

  // Functional equivalence (core check)
  a_func: assert property (known_all |-> (Y == y_exp))
    else $error("Y != spec expression");

  // X-propagation sanity: known inputs imply known output
  a_known: assert property (known_in |-> !$isunknown(Y))
    else $error("Y unknown while inputs known");

  // Per-input monotonicity (only that input changes by +1, others stable)
  a_A_inc: assert property ( known_in && $past(known_in) &&
                             $stable({B,C,D,E,F,G,H}) &&
                             (A == $past(A) + 8'h1)
                           |-> (Y == (($past(Y) + 8'h1)[7:0])) );

  a_B_inc: assert property ( known_in && $past(known_in) &&
                             $stable({A,C,D,E,F,G,H}) &&
                             (B == $past(B) + 8'h1)
                           |-> (Y == (($past(Y) + 8'h1)[7:0])) );

  a_C_inc: assert property ( known_in && $past(known_in) &&
                             $stable({A,B,D,E,F,G,H}) &&
                             (C == $past(C) + 8'h1)
                           |-> (Y == (($past(Y) - 8'h1)[7:0])) );

  a_D_inc: assert property ( known_in && $past(known_in) &&
                             $stable({A,B,C,E,F,G,H}) &&
                             (D == $past(D) + 8'h1)
                           |-> (Y == (($past(Y) - 8'h1)[7:0])) );

  a_E_inc: assert property ( known_in && $past(known_in) &&
                             $stable({A,B,C,D,F,G,H}) &&
                             (E == $past(E) + 8'h1)
                           |-> (Y == (($past(Y) + 8'h1)[7:0])) );

  a_F_inc: assert property ( known_in && $past(known_in) &&
                             $stable({A,B,C,D,E,G,H}) &&
                             (F == $past(F) + 8'h1)
                           |-> (Y == (($past(Y) + 8'h1)[7:0])) );

  a_G_inc: assert property ( known_in && $past(known_in) &&
                             $stable({A,B,C,D,E,F,H}) &&
                             (G == $past(G) + 8'h1)
                           |-> (Y == (($past(Y) - 8'h1)[7:0])) );

  a_H_inc: assert property ( known_in && $past(known_in) &&
                             $stable({A,B,C,D,E,F,G}) &&
                             (H == $past(H) + 8'h1)
                           |-> (Y == (($past(Y) - 8'h1)[7:0])) );

  // Targeted coverage
  c_ab_ov:  cover property (ovAB);
  c_cd_ov:  cover property (ovCD);
  c_ef_ov:  cover property (ovEF);
  c_gh_ov:  cover property (ovGH);
  c_y0:     cover property (Y == 8'h00);
  c_yff:    cover property (Y == 8'hFF);
  c_y80:    cover property (Y == 8'h80);

endmodule

// Example bind (hook up clk from your environment)
// bind multi_input_output multi_input_output_sva u_sva(.clk(clk), .A(A), .B(B), .C(C), .D(D), .E(E), .F(F), .G(G), .H(H), .Y(Y));