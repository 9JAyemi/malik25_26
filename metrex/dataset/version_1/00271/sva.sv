// SVA checker for DFF_with_CLR_E
module DFF_with_CLR_E_sva (
  input logic D, C, E, CLR, Q
);
  default clocking cb @(posedge C); endclocking

  // Async clear: immediate to 0 and dominant
  assert property (@(posedge CLR) ##0 (Q == 1'b0));
  assert property (@(posedge C) CLR |-> ##0 (Q == 1'b0));

  // Synchronous behavior when not in clear
  assert property ((!CLR && !E) |-> ##0 (Q == D));          // capture when enabled (E=0)
  assert property ((!CLR &&  E) |-> ##0 (Q == $past(Q)));   // hold when disabled (E=1)

  // Q changes only on posedge C (with enable) or posedge CLR
  assert property (@(posedge C or posedge CLR)
                   $changed(Q) |-> ($rose(CLR) || ($rose(C) && !CLR && !E)));

  // Q should be known
  assert property (@(posedge C or posedge CLR) !$isunknown(Q));

  // Coverage
  cover property (@(posedge C) (!CLR && !E) ##0 (Q == D));                      // enabled capture
  cover property (@(posedge C) (!CLR &&  E) ##0 (Q == $past(Q)));               // disabled hold
  cover property (@(posedge CLR) $past(Q) && ##0 (Q == 1'b0));                  // async clear from 1->0
  cover property (@(posedge C) $past(CLR) && !CLR && !E ##0 (Q == D));          // release then capture
endmodule

bind DFF_with_CLR_E DFF_with_CLR_E_sva sva_i (.*);