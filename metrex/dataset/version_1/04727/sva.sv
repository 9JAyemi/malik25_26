// SVA for spi_clgen
// Bind into DUT to check functionality and provide concise coverage
bind spi_clgen spi_clgen_sva();

module spi_clgen_sva;

  // Local widths inferred from DUT
  localparam int W_CNT = $bits(cnt);
  localparam int W_DIV = $bits(divider);

  // Default clocking/reset for assertions
  default clocking cb @(posedge clk_in); endclocking
  default disable iff (rst);

  // Helpful lets for readability
  let oneW      = {{W_CNT-1{1'b0}},1'b1};
  let zeroW     = {W_CNT{1'b0}};
  let zeroDIV   = {W_DIV{1'b0}};
  let cond_tog  = (enable && cnt_zero && (!last_clk || clk_out));
  let epos      = (enable && !clk_out && cnt_one) || (!(|divider) && clk_out) || (!(|divider) && go && !enable);
  let eneg      = (enable &&  clk_out && cnt_one) || (!(|divider) && !clk_out && enable);

  // Reset value checks (active while rst is high)
  assert property (@(posedge clk_in) rst |-> (cnt == {W_CNT{1'b1}} && clk_out==1'b0 && pos_edge==1'b0 && neg_edge==1'b0));
  assert property (@(posedge clk_in) rst |=> (cnt == {W_CNT{1'b1}} && clk_out==1'b0 && pos_edge==1'b0 && neg_edge==1'b0));

  // cnt_zero / cnt_one correctness
  assert property (cnt_zero == (cnt == zeroW));
  assert property (cnt_one  == (cnt == oneW));

  // Divider zero detect consistent with reduction OR
  assert property ( (!(|divider)) == (divider == zeroDIV) );

  // Counter behavior
  assert property ( (!enable || cnt_zero) |=> (cnt == $past(divider)) );
  assert property ( ( enable && !cnt_zero) |=> (cnt == $past(cnt) - oneW) );

  // clk_out toggle behavior
  assert property ( cond_tog  |=> (clk_out != $past(clk_out)) );
  assert property ( !cond_tog |=> (clk_out == $past(clk_out)) );

  // Explicit last_clk gating corner checks
  assert property ( enable && cnt_zero && last_clk && !clk_out |=> (clk_out == $past(clk_out)) );
  assert property ( enable && cnt_zero && last_clk &&  clk_out |=> (clk_out != $past(clk_out)) );

  // pos_edge / neg_edge functional equivalence
  assert property ( pos_edge == epos );
  assert property ( neg_edge == eneg );

  // pos_edge and neg_edge are mutually exclusive
  assert property ( !(pos_edge && neg_edge) );

  // For divider != 0, pos_edge/neg_edge are one-cycle pulses
  assert property ( (divider != zeroDIV && pos_edge) |=> !pos_edge );
  assert property ( (divider != zeroDIV && neg_edge) |=> !neg_edge );

  // Coverage: key behaviors
  cover property ( enable && !cnt_zero ##1 (cnt == $past(cnt) - oneW) );                 // decrement path
  cover property ( cnt_zero ##1 (cnt == $past(divider)) );                               // reload on zero
  cover property ( !enable ##1 (cnt == $past(divider)) );                                // reload on disable
  cover property ( enable && cnt_zero && !last_clk ##1 (clk_out != $past(clk_out)) );    // toggle when allowed
  cover property ( enable && cnt_zero && last_clk && !clk_out ##1 (clk_out == $past(clk_out)) ); // gated hold
  cover property ( enable && !clk_out && cnt_one && (divider != zeroDIV) && pos_edge );  // regular pos_edge path
  cover property ( enable &&  clk_out && cnt_one && (divider != zeroDIV) && neg_edge );  // regular neg_edge path
  cover property ( (divider == zeroDIV) && clk_out && pos_edge );                        // zero-divider pos term
  cover property ( (divider == zeroDIV) && !clk_out && enable && neg_edge );             // zero-divider neg term
  cover property ( (divider == zeroDIV) && go && !enable && pos_edge );                  // zero-divider go pulse

endmodule