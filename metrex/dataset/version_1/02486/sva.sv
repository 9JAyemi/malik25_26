// SVA for top_module
module top_module_sva;
  // Bound into top_module scope; can directly see clk, d, sel, q, q_int, dff_sel
  bit neg_init, pos_init;
  always @(negedge clk) neg_init <= 1'b1;
  always @(posedge clk) pos_init <= 1'b1;

  // Shift register behavior (sampled at negedge)
  assert property (@(negedge clk)
    neg_init && !$isunknown($past(q_int)) |-> q_int == { $past(q_int)[6:0], d[0] }
  );

  // Up/down 4-bit counter behavior with wrap (sampled at negedge)
  assert property (@(negedge clk)
    neg_init && sel  && !$isunknown($past(dff_sel)) |-> dff_sel == $past(dff_sel) + 4'd1
  );
  assert property (@(negedge clk)
    neg_init && !sel && !$isunknown($past(dff_sel)) |-> dff_sel == $past(dff_sel) - 4'd1
  );

  // Output mux correctness (check on both edges to catch glitches)
  assert property (@(posedge clk)
    q == (dff_sel[3] ? {q_int[7:4], q_int[3:0]} : {q_int[3:0], q_int[7:4]})
  );
  assert property (@(negedge clk)
    q == (dff_sel[3] ? {q_int[7:4], q_int[3:0]} : {q_int[3:0], q_int[7:4]})
  );

  // Basic X-prop guard on output after activity
  assert property (@(posedge clk) pos_init |-> !$isunknown(q));

  // Coverage
  // Shift observed with both input values
  cover property (@(negedge clk)
    neg_init && !$isunknown($past(q_int)) && q_int == { $past(q_int)[6:0], 1'b1 }
  );
  cover property (@(negedge clk)
    neg_init && !$isunknown($past(q_int)) && q_int == { $past(q_int)[6:0], 1'b0 }
  );
  // Up/down wrap-around
  cover property (@(negedge clk)
    neg_init && sel  && !$isunknown($past(dff_sel)) && $past(dff_sel)==4'hF && dff_sel==4'h0
  );
  cover property (@(negedge clk)
    neg_init && !sel && !$isunknown($past(dff_sel)) && $past(dff_sel)==4'h0 && dff_sel==4'hF
  );
  // Both mux selections exercised
  cover property (@(posedge clk) dff_sel[3]==1'b0 && q == {q_int[3:0], q_int[7:4]});
  cover property (@(posedge clk) dff_sel[3]==1'b1 && q == {q_int[7:4], q_int[3:0]});
endmodule

bind top_module top_module_sva sva_top_module();