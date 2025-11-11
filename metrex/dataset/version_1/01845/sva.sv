// SVA for flipflop_preset_clear
module flipflop_preset_clear_sva (
    input CLK,
    input D,
    input PRE,
    input CLR,
    input Q,
    input Q_bar
);
  default clocking cb @(posedge CLK); endclocking

  // Functional behavior and priority
  assert property ( PRE |-> ##0 (Q == 1'b1) );
  assert property ( (!PRE && CLR) |-> ##0 (Q == 1'b0) );
  assert property ( (!PRE && !CLR) |-> ##0 (Q == D) );
  assert property ( (PRE && CLR) |-> ##0 (Q == 1'b1) ); // PRE dominates CLR

  // Output relationship
  assert property ( Q_bar === ~Q );

  // Synchronous update only on posedge CLK
  assert property ( $changed(Q) |-> $rose(CLK) );

  // Known-control implies known result after update
  assert property ( !$isunknown({PRE,CLR,D}) |-> ##0 !$isunknown(Q) );

  // Coverage
  cover property ( PRE ##0 (Q == 1'b1) );
  cover property ( (!PRE && CLR) ##0 (Q == 1'b0) );
  cover property ( (!PRE && !CLR) ##0 (Q == D) );
  cover property ( (PRE && CLR) ##0 (Q == 1'b1) );
  cover property ( (!PRE && !CLR && D==1'b0) ##1 (!PRE && !CLR && D==1'b1) ); // data-driven 0->1
endmodule

// Example bind:
// bind flipflop_preset_clear flipflop_preset_clear_sva sva_i(.CLK(CLK), .D(D), .PRE(PRE), .CLR(CLR), .Q(Q), .Q_bar(Q_bar));