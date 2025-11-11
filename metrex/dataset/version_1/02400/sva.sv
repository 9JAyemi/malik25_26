// SVA for top_module. Bind this file to the DUT.
// Focused, high-quality checks + key functional coverage.

module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        enable,
  input  logic        sub,
  input  logic        select,
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic [3:0]  counter,
  input  logic [3:0]  sum,
  input  logic [3:0]  max_value,
  input  logic [3:0]  Q
);

  // Basic sanity: no X/Z on key signals
  assert property (@(posedge clk) !$isunknown({reset, enable, sub, select}));
  assert property (@(posedge clk) !$isunknown({A,B}));
  assert property (@(posedge clk) !$isunknown({counter,sum,max_value,Q}));

  // Asynchronous reset must clear counter immediately and at clock edges
  assert property (@(posedge reset) counter == 4'h0);
  assert property (@(posedge clk) reset |-> (counter == 4'h0));

  // Counter behavior: increment/hold, synchronous enable; wrap allowed
  assert property (@(posedge clk) disable iff (reset)
                   enable |-> counter == $past(counter) + 4'd1);
  assert property (@(posedge clk) disable iff (reset)
                   !enable |-> counter == $past(counter));

  // Adder/subtractor correctness (4-bit modular arithmetic)
  assert property (@(posedge clk) sum == (sub ? (A - B) : (A + B)));

  // Max selection correctness
  assert property (@(posedge clk) !select |-> (max_value == counter));
  assert property (@(posedge clk) select |-> (
                     (counter >  sum) ? (max_value == counter) :
                                        (max_value == sum)
                   ));
  // Tie-break (explicit): when equal and selected, choose sum
  assert property (@(posedge clk) select && (counter == sum) |-> (max_value == sum));

  // Output must mirror selected max_value
  assert property (@(posedge clk) Q == max_value);

  // Also directly check Q against spec for robustness
  assert property (@(posedge clk)
                   !select |-> (Q == counter));
  assert property (@(posedge clk)
                   select  |-> (Q == ((counter > sum) ? counter : sum)));

  // Functional coverage (concise, key scenarios)
  // Reset activity
  cover property (@(posedge clk) reset ##1 !reset);
  // Counter wrap-around under enable
  cover property (@(posedge clk) disable iff (reset)
                  enable && ($past(counter)==4'hF) ##1 (counter==4'h0));
  // Adder wrap-around (addition)
  cover property (@(posedge clk) !sub && (sum < A));
  // Subtractor wrap-around (borrow)
  cover property (@(posedge clk) sub && (A < B));
  // Selection paths: counter wins, sum wins, tie
  cover property (@(posedge clk) select && (counter >  sum));
  cover property (@(posedge clk) select && (counter <  sum));
  cover property (@(posedge clk) select && (counter == sum));
  // Mode toggles
  cover property (@(posedge clk) $rose(sub));
  cover property (@(posedge clk) $rose(select));

endmodule

// Bind into the DUT (names match internal signals: counter, sum, max_value)
bind top_module top_module_sva sva_inst(.*);