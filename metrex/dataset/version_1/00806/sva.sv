// SVA for rotator, counter, and and_gate
// Concise, high-quality checks with key corner cases and coverage

// ---------------- rotator ----------------
module rotator_sva (
  input logic        clk,
  input logic        load,
  input logic [1:0]  ena,
  input logic [99:0] data,
  input logic [99:0] out,
  input logic [99:0] shift_reg
);
  default clocking cb @(posedge clk); endclocking

  bit inited;
  initial inited = 0;
  always_ff @(posedge clk) inited <= 1;
  default disable iff (!inited);

  // Output is 1-cycle delayed view of shift_reg
  assert property (out == $past(shift_reg))
    else $error("rotator: out must equal previous shift_reg");

  // Load has priority
  assert property (load |=> shift_reg == data)
    else $error("rotator: load must capture data");

  // No change when disabled
  assert property (!load && (ena == 2'b00) |=> shift_reg == $past(shift_reg))
    else $error("rotator: disabled state changed shift_reg");

  // ena[0]=1 (only) => left rotate by 1
  assert property (!load && (ena == 2'b01)
                   |=> shift_reg == {$past(shift_reg[98:0]), $past(shift_reg[99])})
    else $error("rotator: ena[0] rotate-left mismatch");

  // ena[1]=1 (only) => behavior per RTL (last assignment wins): {1:99,0}
  assert property (!load && (ena == 2'b10)
                   |=> shift_reg == {$past(shift_reg[1:99]), $past(shift_reg[0])})
    else $error("rotator: ena[1] rotate (per RTL) mismatch");

  // Both enables set => second assignment wins (same as ena==2'b10)
  assert property (!load && (ena == 2'b11)
                   |=> shift_reg == {$past(shift_reg[1:99]), $past(shift_reg[0])})
    else $error("rotator: both-enables behavior mismatch");

  // Knownness
  assert property (!$isunknown(out)) else $error("rotator: out is X/Z");

  // Coverage
  cover property (load);
  cover property (!load && ena == 2'b01);
  cover property (!load && ena == 2'b10);
  cover property (!load && ena == 2'b11);
endmodule

bind rotator rotator_sva rotator_sva_i (
  .clk(clk), .load(load), .ena(ena), .data(data), .out(out), .shift_reg(shift_reg)
);

// ---------------- counter ----------------
module counter_sva (
  input logic       clk,
  input logic       reset,
  input logic [3:0] out
);
  default clocking cb @(posedge clk); endclocking

  bit inited;
  initial inited = 0;
  always_ff @(posedge clk) inited <= 1;
  default disable iff (!inited);

  // Synchronous reset dominates
  assert property (reset |=> out == 4'h0)
    else $error("counter: reset did not drive 0 next cycle");

  // Increment (wraps naturally in 4 bits)
  assert property (!reset |=> out == $past(out) + 4'h1)
    else $error("counter: increment mismatch");

  // Knownness
  assert property (!$isunknown(out)) else $error("counter: out is X/Z");

  // Coverage
  cover property (reset);
  cover property (!reset && $past(out) == 4'hF && out == 4'h0);
endmodule

bind counter counter_sva counter_sva_i (
  .clk(clk), .reset(reset), .out(out)
);

// ---------------- and_gate ----------------
// Combinational functional check using event-based sampling
module and_gate_sva (
  input logic [99:0] in1,
  input logic [3:0]  in2,
  input logic [99:0] out
);
  // Check the exact RTL function (note: (in2<<96) is 4-bit, so mask collapses to 0)
  assert property (@(in1 or in2 or out) out == (in1 & (in2 << 96)))
    else $error("and_gate: out != in1 & (in2<<96) (per RTL)");

  // Coverage
  cover property (@(in1 or in2 or out) in2 != 4'h0);
  cover property (@(in1 or in2 or out) out == 100'b0);
endmodule

bind and_gate and_gate_sva and_gate_sva_i (
  .in1(in1), .in2(in2), .out(out)
);

// ---------------- top-level connectivity (optional but concise) ----------------
module top_module_sva (
  input logic        clk,
  input logic        load,
  input logic [3:0]  counter_out,
  input logic [99:0] rotator_out,
  input logic [99:0] final_out
);
  default clocking cb @(posedge clk); endclocking

  bit inited;
  initial inited = 0;
  always_ff @(posedge clk) inited <= 1;
  default disable iff (!inited);

  // Connectivity: final_out must match submodule function per RTL
  assert property (final_out == (rotator_out & (counter_out << 96)))
    else $error("top: final_out connectivity/function mismatch");

  // Counter reset tied to load
  assert property (load |=> counter_out == 4'h0)
    else $error("top: counter_out not reset by load");

  // Coverage
  cover property (load);
  cover property (final_out == 100'b0);
endmodule

bind top_module top_module_sva top_module_sva_i (
  .clk(clk), .load(load),
  .counter_out(counter_out), .rotator_out(rotator_out), .final_out(final_out)
);