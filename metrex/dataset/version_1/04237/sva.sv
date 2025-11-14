// SVA for sky130_fd_sc_lp__and4
// Bindable checker with concise yet complete checks and coverage

checker and4_chk (input logic A, B, C, D, X, input logic and0_out_X);

  // Sample on any input or output edge
  `define AND4_EV (posedge A or negedge A or \
                    posedge B or negedge B or \
                    posedge C or negedge C or \
                    posedge D or negedge D or \
                    posedge X or negedge X)

  // Functional correctness (known inputs => correct X)
  assert property (@(`AND4_EV)
    !$isunknown({A,B,C,D}) |-> (X === (A & B & C & D))
  );

  // Determinism: known inputs => known output
  assert property (@(`AND4_EV)
    !$isunknown({A,B,C,D}) |-> !$isunknown(X)
  );

  // If X is X/Z, at least one input must be X/Z
  assert property (@(`AND4_EV)
    $isunknown(X) |-> $isunknown({A,B,C,D})
  );

  // Buffer correctness and internal net check
  assert property (@(`AND4_EV) X === and0_out_X);
  assert property (@(`AND4_EV)
    !$isunknown({A,B,C,D}) |-> (and0_out_X === (A & B & C & D))
  );

  // Input and output toggle coverage
  cover property (@(posedge A) 1);
  cover property (@(negedge A) 1);
  cover property (@(posedge B) 1);
  cover property (@(negedge B) 1);
  cover property (@(posedge C) 1);
  cover property (@(negedge C) 1);
  cover property (@(posedge D) 1);
  cover property (@(negedge D) 1);
  cover property (@(posedge X) 1);
  cover property (@(negedge X) 1);

  // Full input-space coverage (all 16 combinations) + correct X
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : CMB
      localparam logic [3:0] V = i[3:0];
      cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
        {A,B,C,D} === V && X === (&V)
      );
    end
  endgenerate

  `undef AND4_EV

endchecker

bind sky130_fd_sc_lp__and4 and4_chk u_and4_chk (
  .A(A), .B(B), .C(C), .D(D), .X(X), .and0_out_X(and0_out_X)
);