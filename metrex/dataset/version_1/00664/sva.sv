// SVA for dff_async_set_clear
module dff_async_set_clear_sva (
  input Q,
  input Q_N,
  input CLK,
  input D,
  input SET,
  input CLR
);

  default clocking cb @(posedge CLK); endclocking

  // Functional correctness and priority on clock edge
  // SET dominates CLR, both override D
  assert property (cb SET |-> (Q == 1'b1))
    else $error("SET did not force Q=1 on posedge CLK");

  assert property (cb (!SET && CLR) |-> (Q == 1'b0))
    else $error("CLR did not force Q=0 on posedge CLK when SET=0");

  assert property (cb (!SET && !CLR) |-> (Q == D))
    else $error("Q did not capture D on posedge CLK when SET=CLR=0");

  assert property (cb (SET && CLR) |-> (Q == 1'b1))
    else $error("SET must dominate CLR when both asserted");

  // Q and Q_N must only change on CLK posedge (no glitches)
  assert property (@(posedge Q or negedge Q) $rose(CLK))
    else $error("Q changed without a CLK posedge");

  assert property (@(posedge Q_N or negedge Q_N) $rose(CLK))
    else $error("Q_N changed without a CLK posedge");

  // Complement output must always match
  assert property (@(posedge Q or negedge Q or posedge Q_N or negedge Q_N)
                   (Q_N === ~Q))
    else $error("Q_N is not the complement of Q");

  // Simple supply sanity (should always hold given supply1/supply0)
  // Uncomment if you want explicit checks when bound above cell-level
  // assert property (cb 1) else ;
  // assert property (cb VPWR && VPB && !VGND && !VNB)
  //   else $error("Supply rails invalid");

  // Coverage: exercise all behavior paths and output toggles
  cover property (cb SET && (Q == 1'b1));
  cover property (cb (!SET && CLR) && (Q == 1'b0));
  cover property (cb (!SET && !CLR) && (D == 1'b1) && (Q == 1'b1));
  cover property (cb (!SET && !CLR) && (D == 1'b0) && (Q == 1'b0));
  cover property (@(posedge CLK) $changed(Q));
  cover property (@(posedge CLK) (SET && CLR));  // simultaneous assertions

endmodule

// Bind into DUT
bind dff_async_set_clear dff_async_set_clear_sva sva_i (
  .Q(Q),
  .Q_N(Q_N),
  .CLK(CLK),
  .D(D),
  .SET(SET),
  .CLR(CLR)
);