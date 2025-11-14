// SVA for mux_2_1
module mux_2_1_sva(input logic A, B, SEL, OUT);

  // Functional correctness (allow delta-cycle settle)
  assert property (@(A or B or SEL) ##0 (OUT === ((SEL === 1'b0) ? A : B)))
    else $error("mux_2_1: OUT != selected input");

  // OUT must be known when selected input is known
  assert property (@(A or B or SEL) ((SEL === 1'b0) && !$isunknown(A)) |-> ##0 (!$isunknown(OUT)))
    else $error("mux_2_1: OUT X/Z with SEL==0 and A known");
  assert property (@(A or B or SEL) ((SEL !== 1'b0) && !$isunknown(B)) |-> ##0 (!$isunknown(OUT)))
    else $error("mux_2_1: OUT X/Z with SEL!=0 and B known");

  // Coverage: both select values and X/Z on SEL
  cover property (@(SEL) SEL === 1'b0);
  cover property (@(SEL) SEL === 1'b1);
  cover property (@(SEL) (SEL !== 1'b0) && (SEL !== 1'b1)); // SEL is X/Z

  // Coverage: data propagation on both paths
  cover property (@(A) (SEL === 1'b0) ##0 (OUT === A));
  cover property (@(B) (SEL !== 1'b0) ##0 (OUT === B));

endmodule

bind mux_2_1 mux_2_1_sva sva_i(.*);