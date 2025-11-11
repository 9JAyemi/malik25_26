// SVA for binary_to_bcd_converter
// Checks reset behavior, bit-slice mapping, numeric equivalence, value bounds, X-checks
// Includes compact functional coverage of all 16 input codes and key boundary/reset events

module binary_to_bcd_converter_sva (
  input clk,
  input reset,
  input [3:0] binary_input,
  input [3:0] msd_output,
  input [3:0] lsd1_output,
  input [3:0] lsd2_output
);

  // Reset: synchronous clear to 0
  assert property (@(posedge clk) reset |-> (msd_output==4'd0 && lsd1_output==4'd0 && lsd2_output==4'd0))
    else $error("Reset did not clear outputs to zero");

  // No X/Z on key signals (checked every cycle)
  assert property (@(posedge clk) !$isunknown({binary_input, msd_output, lsd1_output, lsd2_output}))
    else $error("X/Z detected on interface signals");

  // Mapping checks (on active cycles)
  assert property (@(posedge clk) disable iff (reset)
                   msd_output  == {3'b000, binary_input[3]})
    else $error("msd_output mismatch");

  assert property (@(posedge clk) disable iff (reset)
                   lsd1_output == {2'b00, binary_input[2:1]})
    else $error("lsd1_output mismatch");

  assert property (@(posedge clk) disable iff (reset)
                   lsd2_output == {3'b000, binary_input[0]})
    else $error("lsd2_output mismatch");

  // Numeric equivalence: 8*MSD + 2*LSD1 + LSD2 == binary_input
  assert property (@(posedge clk) disable iff (reset)
                   ($unsigned(msd_output)*8 + $unsigned(lsd1_output)*2 + $unsigned(lsd2_output))
                     == $unsigned(binary_input))
    else $error("Weighted-sum equivalence failed");

  // Output value bounds (sanity)
  assert property (@(posedge clk) disable iff (reset) msd_output  inside {[4'd0:4'd1]});
  assert property (@(posedge clk) disable iff (reset) lsd1_output inside {[4'd0:4'd3]});
  assert property (@(posedge clk) disable iff (reset) lsd2_output inside {[4'd0:4'd1]});

  // Functional coverage

  // Hit all 16 input values when active
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_cov_in
      localparam logic [3:0] V = i[3:0];
      cover property (@(posedge clk) disable iff (reset) binary_input == V);
    end
  endgenerate

  // Boundary transition coverage: 7 -> 8 (MSD flips 0->1)
  cover property (@(posedge clk) disable iff (reset)
                  $past(binary_input)==4'h7 && binary_input==4'h8);

  // Reset activity coverage
  cover property (@(posedge clk) $rose(reset));
  cover property (@(posedge clk) $fell(reset));

endmodule

// Bind into the DUT
bind binary_to_bcd_converter binary_to_bcd_converter_sva sva_inst(.*);