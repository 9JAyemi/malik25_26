// SVA for or_sleep. Bind this to the DUT.
// Functional check + focused coverage; no TB code needed.

module or_sleep_sva (
  input logic A,
  input logic SLEEP,
  input logic X,
  input logic B
);

  // Core functional equivalence (4-state correct): X == (~SLEEP) & A
  property p_func;
    @(posedge A or negedge A or posedge SLEEP or negedge SLEEP or posedge X or negedge X)
      X === ((!SLEEP) & A);
  endproperty
  assert property (p_func);

  // B must be tied-off low
  property p_B_const;
    @(posedge A or negedge A or posedge SLEEP or negedge SLEEP or posedge X or negedge X)
      B === 1'b0;
  endproperty
  assert property (p_B_const);

  // Sleep dominates output
  property p_sleep_forces_0;
    @(posedge A or negedge A or posedge SLEEP or negedge SLEEP)
      (SLEEP === 1'b1) |-> (X === 1'b0);
  endproperty
  assert property (p_sleep_forces_0);

  // When not sleeping and A is known, X follows A
  property p_awake_follows_A;
    @(posedge A or negedge A or posedge SLEEP or negedge SLEEP)
      (SLEEP === 1'b0 && !$isunknown(A)) |-> (X === A);
  endproperty
  assert property (p_awake_follows_A);

  // X cannot rise while sleeping
  property p_no_rise_in_sleep;
    @(posedge X) SLEEP === 1'b0;
  endproperty
  assert property (p_no_rise_in_sleep);

  // ----------------
  // Functional coverage
  // ----------------

  // Cover all input/output combinations
  cover property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP) (SLEEP==1'b0 && A==1'b0 && X==1'b0));
  cover property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP) (SLEEP==1'b0 && A==1'b1 && X==1'b1));
  cover property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP) (SLEEP==1'b1 && A==1'b0 && X==1'b0));
  cover property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP) (SLEEP==1'b1 && A==1'b1 && X==1'b0));

  // Cover key transitions
  cover property (@(posedge SLEEP) X==1'b0);      // enter sleep forces low
  cover property (@(negedge SLEEP) X==A);         // exit sleep follows A
  cover property (@(posedge A) (SLEEP==1'b0 && X==1'b1));
  cover property (@(negedge A) (SLEEP==1'b0 && X==1'b0));

  // Optional: observe X unknown when SLEEP is X and A is 1 (4-state merge)
  cover property (@(posedge A or negedge A or posedge SLEEP or negedge SLEEP)
                  (SLEEP===1'bx && A==1'b1 && $isunknown(X)));

endmodule

// Bind example (place in a package or a top-level SV file)
// bind or_sleep or_sleep_sva sva_i (.A(A), .SLEEP(SLEEP), .X(X), .B(B));