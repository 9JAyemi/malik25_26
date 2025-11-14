// SVA for top_module
// Bind into the DUT to check reset, shifting, capture behavior, multiply timing, and output integrity.

module top_module_sva;

  // Clocking and reset come from bound scope (top_module)
  // Assertions

  // 1) Reset behavior: all state clears to 0 one cycle after reset sampled high
  assert property (@(posedge clk)
    reset |=> (shift_reg[0]==8'h00 && shift_reg[1]==8'h00 &&
               shift_reg[2]==8'h00 && shift_reg[3]==8'h00 &&
               capture_reg==32'h0000_0000 && product==32'h0000_0000 && out==32'h0000_0000)
  ) else $error("Reset did not clear all state to 0");

  // 2) Shift register stage-by-stage timing (next-state equals current sources)
  assert property (@(posedge clk) disable iff (reset)
    shift_reg[0] == $past(d)
  ) else $error("Shift stage 0 load mismatch");
  assert property (@(posedge clk) disable iff (reset)
    shift_reg[1] == $past(shift_reg[0])
  ) else $error("Shift stage 1 mismatch");
  assert property (@(posedge clk) disable iff (reset)
    shift_reg[2] == $past(shift_reg[1])
  ) else $error("Shift stage 2 mismatch");
  assert property (@(posedge clk) disable iff (reset)
    shift_reg[3] == $past(shift_reg[2])
  ) else $error("Shift stage 3 mismatch");

  // Optional end-to-end shift check
  assert property (@(posedge clk) disable iff (reset)
    shift_reg[3] == $past(d,3)
  ) else $error("Shift pipeline end-to-end mismatch (3-cycle)");


  // 3) Rising-edge capture behavior
  // a) When condition true, capture next equals current in
  assert property (@(posedge clk) disable iff (reset)
    (in[31] && !capture_reg[31]) |=> (capture_reg == $past(in))
  ) else $error("Capture on rising condition failed");
  // b) When condition false, capture holds
  assert property (@(posedge clk) disable iff (reset)
    !(in[31] && !capture_reg[31]) |=> (capture_reg == $past(capture_reg))
  ) else $error("Capture register changed without enable");
  // c) Capture MSB can only rise (never fall) without reset
  assert property (@(posedge clk) disable iff (reset)
    !$fell(capture_reg[31])
  ) else $error("capture_reg[31] fell without reset");
  // d) If capture_reg changed, it was due to the enable
  assert property (@(posedge clk) disable iff (reset)
    (capture_reg != $past(capture_reg)) |-> $past(in[31] && !$past(capture_reg[31]))
  ) else $error("capture_reg changed without proper condition");


  // 4) Multiply timing and truncation to 32b
  assert property (@(posedge clk) disable iff (reset)
    product == ($past(shift_reg[3]) * $past(capture_reg))[31:0]
  ) else $error("Product timing/value mismatch");

  // 5) out mirrors product combinationally
  assert property (@(posedge clk)
    out == product
  ) else $error("out != product");

  // 6) Known output after reset deassertion
  assert property (@(posedge clk) disable iff (reset)
    !$isunknown(out)
  ) else $error("out has X/Z after reset deassertion");


  // Coverage

  // C1: Observe a valid capture event
  cover property (@(posedge clk) !reset && in[31] && !capture_reg[31]);

  // C2: See a value propagate through the 4-stage shift to stage 3
  cover property (@(posedge clk) !reset && (d!=0) ##3 (shift_reg[3] == $past(d,3)));

  // C3: Non-zero product after capture occurred
  cover property (@(posedge clk) !reset
    ##1 (in[31] && !capture_reg[31]) ##1 (product != 32'h0)
  );

endmodule

bind top_module top_module_sva u_top_module_sva();