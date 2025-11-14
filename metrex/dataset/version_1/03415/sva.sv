// SVA for Reset_Delay
// Checks async reset, counter behavior, and oRESET semantics; includes key covers.

module Reset_Delay_sva #(parameter MAX = 28'h4FFFFFF)
  (input iCLK, input iRST, input oRESET, input [27:0] Cont);

  default clocking cb @(posedge iCLK); endclocking

  bit past_valid;
  always @(posedge iCLK) past_valid <= 1'b1;

  // Async reset clears immediately
  assert property (@(negedge iRST) (oRESET==1'b0 && Cont==28'b0));

  // While reset held low, hold zeros
  assert property (@cb !iRST |-> (oRESET==1'b0 && Cont==28'b0));

  // Counter increments by 1 modulo 2^28 when out of reset
  assert property (@cb disable iff (!iRST || !past_valid)
                   Cont == $past(Cont) + 28'd1);

  // oRESET behavior: goes high on first clock after reset release and never falls while out of reset
  assert property (@cb $rose(iRST) |-> oRESET==1'b1);
  assert property (@cb disable iff(!iRST) oRESET==1'b1);
  assert property (@cb disable iff(!iRST) !$fell(oRESET));

  // When previous Cont==MAX, oRESET holds its previous value (no assignment in RTL)
  assert property (@cb disable iff(!iRST)
                   ($past(Cont)==MAX) |-> oRESET==$past(oRESET));

  // No X/Z during normal operation
  assert property (@cb disable iff(!iRST) !$isunknown({oRESET,Cont}));

  // Coverage: reset release, reaching MAX, wrap to 0, and reset-to-release behavior
  cover property (@cb $rose(iRST));
  cover property (@cb $rose(iRST) ##[1:$] (Cont==MAX));
  cover property (@cb (Cont==MAX) ##1 (Cont==28'b0));
  cover property (@cb (!iRST && oRESET==1'b0) ##1 $rose(iRST) ##1 (oRESET==1'b1));

endmodule

bind Reset_Delay Reset_Delay_sva #(.MAX(28'h4FFFFFF)) sva_i (.*);