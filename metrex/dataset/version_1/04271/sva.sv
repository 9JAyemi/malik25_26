// SystemVerilog Assertions for the given design
// Bind once at top; covers internal relationships and all key behaviors concisely.

module top_module_sva #(parameter int PERIOD = 16) (
  input  logic        clk,
  input  logic        reset,
  input  logic        select,
  input  logic [7:0]  a,
  input  logic [7:0]  b,
  input  logic [7:0]  q,
  input  logic [7:0]  adder_out,
  input  logic [3:0]  counter_out,
  input  logic [7:0]  sum
);
  default clocking cb @(posedge clk); endclocking

  // Sanity/X checks
  assert property ( !$isunknown({reset,select,a,b}) );
  assert property ( (!$isunknown({reset,select,a,b})) |-> !$isunknown({adder_out,sum,q}) );

  // Adder correctness (8-bit modulo add)
  assert property ( adder_out == (a + b) );

  // Counter behavior (synchronous reset, increment, wrap, range)
  assert property ( reset |-> (counter_out == 0) );
  assert property ( counter_out < PERIOD );
  assert property ( disable iff (reset) ($past(counter_out) == PERIOD-1) |-> (counter_out == 0) );
  assert property ( disable iff (reset) ($past(counter_out) != PERIOD-1) |-> (counter_out == $past(counter_out) + 1) );
  cover  property ( counter_out == PERIOD-1 ##1 counter_out == 0 );

  // Functional block (as coded) and note shift semantics
  assert property ( sum == (adder_out + (counter_out << 8)) );
  assert property ( (counter_out << 8) == 0 ); // 4-bit << 8 is always zero
  cover  property ( sum == adder_out );

  // Control block (branch behavior)
  assert property ( select  |-> ( q == sum + (counter_out << 8) ) );
  assert property ( !select |-> ( q == sum + adder_out ) );

  // End-to-end datapath (as implemented)
  assert property ( q == ( select ? adder_out : (adder_out + adder_out) ) );

  // q is independent of counter_out in this implementation
  assert property ( $stable(a) && $stable(b) && $stable(select) && !$stable(counter_out) |-> (q == $past(q)) );

  // Coverage: exercise both branches and adder overflow wrap
  cover property ( select );
  cover property ( !select );
  cover property ( (a + b) < a );
endmodule

bind top_module top_module_sva #(.PERIOD(16)) top_module_sva_i (
  .clk        (clk),
  .reset      (reset),
  .select     (select),
  .a          (a),
  .b          (b),
  .q          (q),
  .adder_out  (adder_out),
  .counter_out(counter_out),
  .sum        (sum)
);