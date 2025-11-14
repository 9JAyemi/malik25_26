// Bind this SVA module to my_module:  bind my_module my_module_sva sva();

// Concise, high-value SVA for my_module
module my_module_sva (my_module dut);

  // Structural sanity: concatenation width vs inv_in
  localparam int CONCAT_W = $bits({dut.in12,dut.in11,dut.in10,dut.in9,dut.in8,dut.in7,dut.in6,dut.in5,dut.in4,dut.in3,dut.in2,dut.in1,dut.in0});
  initial assert (CONCAT_W == $bits(dut.inv_in))
    else $warning("Width mismatch: inv_in (%0d) <- ~concat (%0d). Truncation is occurring.", $bits(dut.inv_in), CONCAT_W);

  // Basic connectivity
  assert property (@(posedge dut.clk) dut.data_out == dut.probe1);
  assert property (@(negedge dut.clk) dut.data_out == dut.probe1);

  // Probe0 captures data_in on each posedge; holds across negedge
  assert property (@(posedge dut.clk) dut.probe0 == $past(dut.data_in));
  assert property (@(negedge dut.clk) $stable(dut.probe0));

  // Probe1 captures probe0 on each negedge; data_out only changes on negedge
  assert property (@(negedge dut.clk) dut.probe1 == $past(dut.probe0));
  assert property (@(posedge dut.clk) $stable(dut.data_out));

  // End-to-end latency: data_out reflects last posedge-sampled data_in at negedge
  assert property (@(negedge dut.clk)
                   !$isunknown($past(dut.data_in, 1, posedge dut.clk))
                   |-> (dut.data_out == $past(dut.data_in, 1, posedge dut.clk)));

  // inv_in behavior (note: truncation to low 13 bits of inverted concat)
  assert property (@(negedge dut.clk) $stable(dut.inv_in)); // only updates on posedge
  assert property (@(posedge dut.clk)
                   dut.inv_in == $past((~{dut.in12,dut.in11,dut.in10,dut.in9,dut.in8,dut.in7,
                                           dut.in6,dut.in5,dut.in4,dut.in3,dut.in2,dut.in1,dut.in0})[12:0]));

  // X-prop hygiene on outputs when a valid posedge sample exists
  assert property (@(negedge dut.clk)
                   !$isunknown($past(dut.data_in, 1, posedge dut.clk)) |-> !$isunknown(dut.data_out));

  // Coverage
  cover property (@(posedge dut.clk)  $changed(dut.data_in));     // stimulus on input
  cover property (@(negedge dut.clk)  $changed(dut.data_out));    // output activity
  cover property (@(negedge dut.clk)
                  dut.data_out == $past(dut.data_in, 1, posedge dut.clk)); // end-to-end observe
  cover property (@(posedge dut.clk)  (|(( {dut.in12,dut.in11,dut.in10,dut.in9,dut.in8,dut.in7,
                                            dut.in6,dut.in5,dut.in4,dut.in3,dut.in2,dut.in1,dut.in0} )[168:13]))); // truncation exercised

endmodule