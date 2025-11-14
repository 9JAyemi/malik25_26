// SVA for top_module and submodules (concise, high-quality checks + essential coverage)

//////////////////////////////////////////////////////////////
// Top-level composition checks
//////////////////////////////////////////////////////////////
module top_module_sva (
  input logic               clk,
  input logic               reset,
  input logic [99:0]        a, b,
  input logic               cin,
  input logic [99:0]        sum,
  input logic [3:0]         counter_out,
  input logic [99:0]        final_sum,
  input logic [99:0]        adder_out
);
  default clocking cb @(posedge clk); endclocking

  // Sum wiring sanity
  assert property (sum == final_sum);

  // End-to-end arithmetic (valid when inputs known)
  assert property (!$isunknown({a,b,cin,counter_out}) |-> sum == (a + b + cin + counter_out));

  // Stability: if inputs stable across a cycle, sum must be stable
  assert property (disable iff (reset) $stable({a,b,cin,counter_out}) |=> $stable(sum));

  // Basic coverage
  cover property (reset ##1 !reset);                 // reset deassertion observed
  cover property (counter_out == 4'hF ##1 counter_out == 4'h0); // wrap observed
endmodule

bind top_module top_module_sva tmsva (
  .clk(clk),
  .reset(reset),
  .a(a),
  .b(b),
  .cin(cin),
  .sum(sum),
  .counter_out(counter_out),
  .final_sum(final_sum),
  .adder_out(adder_out)
);

//////////////////////////////////////////////////////////////
/* binary_counter assertions */
//////////////////////////////////////////////////////////////
module binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  out
);
  default clocking cb @(posedge clk); endclocking

  // Sync reset dominates
  assert property (reset |-> out == 4'd0);

  // Increment-by-1 each enabled cycle
  assert property (disable iff (reset) out == $past(out) + 4'd1);

  // Wrap from 15 -> 0
  assert property (disable iff (reset) $past(out) == 4'hF |-> out == 4'h0);

  // No X/Z on output when clocking
  assert property (!$isunknown(out));

  // Coverage
  cover property (reset);
  cover property (!reset [*5]);          // saw a run of increments
  cover property ($past(out)==4'hE |-> out==4'hF ##1 out==4'h0); // near-wrap and wrap
endmodule

bind binary_counter binary_counter_sva bcsva (
  .clk(clk),
  .reset(reset),
  .out(out)
);

//////////////////////////////////////////////////////////////
/* binary_adder assertions */
//////////////////////////////////////////////////////////////
module binary_adder_sva (
  input  logic [99:0] a, b,
  input  logic        cin,
  input  logic [99:0] sum,
  input  logic        cout
);
  // Combinational correctness: fire on any input change
  assert property (@(a or b or cin) {cout, sum} == a + b + cin);

  // Known-inputs imply known-outputs
  assert property (@(a or b or cin) !$isunknown({a,b,cin}) |-> !$isunknown({sum,cout}));

  // Coverage
  cover property (@(posedge cout) 1);             // carry-out observed
  cover property (@(a or b or cin) cin);          // cin used
  cover property (@(a or b or cin) sum == '0);    // zero sum case observed
endmodule

bind binary_adder binary_adder_sva basva (
  .a(a),
  .b(b),
  .cin(cin),
  .sum(sum),
  .cout(cout)
);

//////////////////////////////////////////////////////////////
/* functional_module assertions */
//////////////////////////////////////////////////////////////
module functional_module_sva (
  input logic [99:0] adder_out,
  input logic [3:0]  counter_out,
  input logic [99:0] final_sum
);
  // Combinational correctness: zero-extend counter
  assert property (@(adder_out or counter_out) final_sum == adder_out + {96'b0, counter_out});

  // Known-inputs imply known-output
  assert property (@(adder_out or counter_out) !$isunknown({adder_out,counter_out}) |-> !$isunknown(final_sum));

  // Coverage
  cover property (@(counter_out) counter_out != 4'd0);
endmodule

bind functional_module functional_module_sva fmsva (
  .adder_out(adder_out),
  .counter_out(counter_out),
  .final_sum(final_sum)
);