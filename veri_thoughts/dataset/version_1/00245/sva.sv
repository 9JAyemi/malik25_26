// SVA for sky130_fd_sc_ls__a311o
// Function: X = (A1 & A2 & A3) | B1 | C1

`define A311O_INPUT_EVT (posedge A1 or negedge A1 or \
                         posedge A2 or negedge A2 or \
                         posedge A3 or negedge A3 or \
                         posedge B1 or negedge B1 or \
                         posedge C1 or negedge C1)

module sky130_fd_sc_ls__a311o_sva
(
  input logic X,
  input logic A1, A2, A3,
  input logic B1, C1
);

  // Functional equivalence (4-state, sampled after delta)
  assert property (@(`A311O_INPUT_EVT) ##0
                   (X === ((A1 & A2 & A3) | B1 | C1)));

  // Dominating OR inputs force X=1 regardless of others
  assert property (@(`A311O_INPUT_EVT) (B1===1'b1) |-> ##0 (X===1'b1));
  assert property (@(`A311O_INPUT_EVT) (C1===1'b1) |-> ##0 (X===1'b1));

  // When B1=C1=0, output equals 3-input AND
  assert property (@(`A311O_INPUT_EVT)
                   ((B1===1'b0) && (C1===1'b0)) |-> ##0
                   (X === (A1 & A2 & A3)));

  // If all inputs are known, output must be known
  assert property (@(`A311O_INPUT_EVT)
                   (!$isunknown({A1,A2,A3,B1,C1})) |-> ##0
                   (!$isunknown(X)));

  // Coverage: each controlling path and all-zero case
  cover property (@(`A311O_INPUT_EVT) ##0
                  ( B1 && !C1 && !(A1 & A2 & A3) && X ));
  cover property (@(`A311O_INPUT_EVT) ##0
                  ( C1 && !B1 && !(A1 & A2 & A3) && X ));
  cover property (@(`A311O_INPUT_EVT) ##0
                  ( !B1 && !C1 &&  A1 && A2 && A3 && X ));
  cover property (@(`A311O_INPUT_EVT) ##0
                  ( !A1 && !A2 && !A3 && !B1 && !C1 && !X ));

endmodule

bind sky130_fd_sc_ls__a311o sky130_fd_sc_ls__a311o_sva
  i_sva ( .X(X), .A1(A1), .A2(A2), .A3(A3), .B1(B1), .C1(C1) );

`undef A311O_INPUT_EVT