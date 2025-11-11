// SVA for top_module (bindable). Focused, high-quality checks and coverage.
module top_module_sva;
  // Access DUT signals via bind (no ports needed)
  // Default SVA settings
  default clocking cb @(posedge clk); endclocking

  // ----------------------
  // Combinational correctness
  // ----------------------
  // internal wiring/mapping
  assert property (data0 == a[3:0]);
  assert property (data1 == b[3:0]);
  assert property (data2 == sum[3:0]);
  assert property (data3 == 4'b0);
  assert property (data4 == 4'b0);
  assert property (data5 == 4'b0);

  // adder correctness
  assert property (sum == a + b);
  assert property (add_overflow == ((a[7] == b[7]) && (sum[7] != a[7])));

  // parity mux correctness (combinational)
  assert property (sel == 3'b000 |-> parity == ^a[3:0]);
  assert property (sel == 3'b001 |-> parity == ^b[3:0]);
  assert property (sel == 3'b010 |-> parity == ^sum[3:0]);
  assert property ((sel inside {3'b011,3'b100,3'b101,3'b110,3'b111}) |-> parity == 1'b0);

  // ----------------------
  // Sequential behavior
  // ----------------------
  // Reset drives outputs low by next cycle
  assert property (@(posedge clk) reset |=> (out == 4'b0 && overflow == 1'b0));

  // All sequential properties disabled during reset
  default disable iff (reset);

  // Registered output selection
  assert property (sel == 3'b000 |=> out == a[3:0]);
  assert property (sel == 3'b001 |=> out == b[3:0]);
  assert property (sel == 3'b010 |=> out == sum[3:0]);

  // Overflow register behavior
  assert property (sel == 3'b010 |=> overflow == add_overflow);
  // For 000/001, overflow retains previous value (design intent per code)
  assert property ((sel inside {3'b000,3'b001}) |=> overflow == $past(overflow));
  // For all other sels (default case), clear outputs
  assert property ((sel inside {3'b011,3'b100,3'b101,3'b110,3'b111}) |=> (out == 4'b0 && overflow == 1'b0));

  // Output nets match regs (continuous assigns)
  assert property (out == out_reg);
  assert property (overflow == overflow_reg);

  // Basic X checks on key controls/outputs at clock
  assert property (!$isunknown(sel));
  assert property (!$isunknown({out, overflow, parity}));

  // ----------------------
  // Coverage
  // ----------------------
  cover property (@(posedge clk) reset ##1 !reset);
  cover property (sel == 3'b000);
  cover property (sel == 3'b001);
  cover property (sel == 3'b010);
  cover property (sel == 3'b011);
  cover property (sel == 3'b100);
  cover property (sel == 3'b101);
  cover property (sel == 3'b110);
  cover property (sel == 3'b111);
  cover property (sel == 3'b010 && add_overflow);       // add overflow case
  cover property (sel == 3'b010 && !add_overflow);      // add no-overflow case
  cover property ($past(sel)==3'b010 && (sel inside {3'b000,3'b001}) && overflow == $past(add_overflow)); // overflow retention after add
endmodule

bind top_module top_module_sva sva_i();