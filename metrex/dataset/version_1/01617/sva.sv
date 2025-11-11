// SVA checker for sky130_fd_sc_ms__and4bb
module sky130_fd_sc_ms__and4bb_sva (
    input X,
    input A_N,
    input B_N,
    input C,
    input D,
    input nor0_out,
    input and0_out_X
);

  // Trigger on any input transition
  `define AND4BB_CLK (posedge A_N or negedge A_N or \
                       posedge B_N or negedge B_N or \
                       posedge C   or negedge C   or \
                       posedge D   or negedge D)

  // Functional equivalence (4-state exact)
  assert property (@(`AND4BB_CLK)
    X === ((~A_N) & (~B_N) & C & D)
  );

  // Structural checks (internal signals)
  assert property (@(`AND4BB_CLK)
    nor0_out    === ~(A_N | B_N)
  );
  assert property (@(`AND4BB_CLK)
    and0_out_X  === (nor0_out & C & D)
  );
  assert property (@(`AND4BB_CLK)
    X           === and0_out_X
  );

  // One-direction implications (useful for debug)
  assert property (@(`AND4BB_CLK)
    (X === 1'b1) |-> ((A_N === 1'b0) && (B_N === 1'b0) && (C === 1'b1) && (D === 1'b1))
  );
  assert property (@(`AND4BB_CLK)
    ((C === 1'b0) || (D === 1'b0) || (A_N === 1'b1) || (B_N === 1'b1)) |-> (X === 1'b0)
  );

  // Knownness: if all inputs known, output must be known
  assert property (@(`AND4BB_CLK)
    !$isunknown({A_N,B_N,C,D}) |-> !$isunknown(X)
  );

  // Coverage
  cover property (@(`AND4BB_CLK) X === 1'b1);         // only one minterm
  cover property (@(`AND4BB_CLK) $rose(X));
  cover property (@(`AND4BB_CLK) $fell(X));
  cover property (@(`AND4BB_CLK) $rose(nor0_out));
  cover property (@(`AND4BB_CLK) $fell(nor0_out));
  cover property (@(`AND4BB_CLK) $rose(and0_out_X));
  cover property (@(`AND4BB_CLK) $fell(and0_out_X));

  `undef AND4BB_CLK
endmodule

// Bind into the DUT (connect internal nets for structural checks)
bind sky130_fd_sc_ms__and4bb sky130_fd_sc_ms__and4bb_sva u_and4bb_sva (
  .X(X),
  .A_N(A_N),
  .B_N(B_N),
  .C(C),
  .D(D),
  .nor0_out(nor0_out),
  .and0_out_X(and0_out_X)
);