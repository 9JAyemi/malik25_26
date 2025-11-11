// SVA for sky130_fd_sc_hdll__and4
// Bindable, concise, with truth-table coverage

module sky130_fd_sc_hdll__and4_sva (
  input logic A, B, C, D,
  input logic X
);

  // Sample on any input edge; evaluate after delta to avoid races
  default clocking cb @(
      posedge A or negedge A or
      posedge B or negedge B or
      posedge C or negedge C or
      posedge D or negedge D
  ); endclocking

  // Functional equivalence (4-state aware)
  assert property (##0 (X === (A & B & C & D)))
    else $error("AND4 functional mismatch: X=%0b A=%b B=%b C=%b D=%b", X, A, B, C, D);

  // Known-propagation: if all inputs known, output must be known
  assert property ( (!$isunknown({A,B,C,D})) |-> ##0 (!$isunknown(X)) )
    else $error("AND4 X-propagation error: inputs known, X unknown");

  // Truth-table coverage: all 16 input combinations observed and output matches
  genvar i;
  for (i = 0; i < 16; i++) begin : tt_cov
    localparam logic [3:0] v = i[3:0];
    cover property (##0 ( {A,B,C,D} === v && X === (A & B & C & D) ));
  end

  // Output toggle coverage
  cover property ( $rose(X) );
  cover property ( $fell(X) );

endmodule

// Bind into DUT
bind sky130_fd_sc_hdll__and4 sky130_fd_sc_hdll__and4_sva and4_sva_i (
  .A(A), .B(B), .C(C), .D(D), .X(X)
);