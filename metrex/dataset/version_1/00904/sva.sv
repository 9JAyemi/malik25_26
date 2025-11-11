// SVA for register_mux. Bind this module to the DUT.
// Example: bind register_mux register_mux_sva sva();

module register_mux_sva;

  // Access DUT scope via bind (uses DUT signal names directly)
  default clocking cb @ (posedge clk); endclocking
  localparam logic [7:0] RESET_VAL = 8'h34;

  // -----------------------------
  // Sequential register behavior
  // -----------------------------
  // Synchronous reset value
  assert property (reset |-> (reg0 == RESET_VAL && reg1 == RESET_VAL));

  // First cycle after reset deassertion: capture current d0/d1
  assert property ($fell(reset) |-> (reg0 == $sampled(d0) && reg1 == $sampled(d1)));

  // Steady-state load (not in or just after reset)
  assert property ((!reset && !$past(reset)) |-> (reg0 == $past(d0) && reg1 == $past(d1)));

  // -----------------------------
  // Mux decode correctness
  // -----------------------------
  assert property ((sel == 3'b000) |-> (mux_out == reg0));
  assert property ((sel == 3'b001) |-> (mux_out == reg1));
  assert property ((sel == 3'b010) |-> (mux_out == data0));
  assert property ((sel == 3'b011) |-> (mux_out == data1));
  assert property ((sel == 3'b100) |-> (mux_out == data2));
  assert property ((sel == 3'b101) |-> (mux_out == data3));
  assert property ((sel == 3'b110) |-> (mux_out == data4));
  assert property ((sel == 3'b111) |-> (mux_out == data5));

  // Output must equal mux_out for all sel values
  assert property (q === mux_out);

  // -----------------------------
  // X-propagation sanity (after reset observed)
  // -----------------------------
  bit seen_rst;
  initial seen_rst = 1'b0;
  always @(posedge clk) if (reset) seen_rst <= 1'b1;

  assert property (seen_rst && !$isunknown({sel,reg0,reg1,data0,data1,data2,data3,data4,data5})
                   |-> !$isunknown(q));

  // -----------------------------
  // Functional coverage
  // -----------------------------
  cover property (reset);
  cover property ($fell(reset));

  // Cover each select path reaches q
  cover property ((sel == 3'b000) && (q == reg0));
  cover property ((sel == 3'b001) && (q == reg1));
  cover property ((sel == 3'b010) && (q == data0));
  cover property ((sel == 3'b011) && (q == data1));
  cover property ((sel == 3'b100) && (q == data2));
  cover property ((sel == 3'b101) && (q == data3));
  cover property ((sel == 3'b110) && (q == data4));
  cover property ((sel == 3'b111) && (q == data5));

  // Cover registers updating from inputs (post-reset steady state)
  cover property ((!reset && !$past(reset)) ##1 (reg0 == $past(d0)));
  cover property ((!reset && !$past(reset)) ##1 (reg1 == $past(d1)));

endmodule