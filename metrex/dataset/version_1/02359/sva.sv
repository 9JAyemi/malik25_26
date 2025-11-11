// SVA for top_module and submodules (bind-friendly, concise, high-signal-coverage)

// ---------- counter_module SVA ----------
module counter_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  q
);
  default clocking cb @(posedge clk); endclocking

  // Synchronous reset drives 0 next cycle
  assert property (reset |=> q == 4'd0);

  // Count up modulo-16 every non-reset cycle (safe-guard $past with $past(1'b1))
  assert property ((!reset && $past(1'b1)) |-> q == $past(q) + 4'd1);

  // No X/Z when not in reset
  assert property (!reset |-> !$isunknown(q));

  // Coverage: reset release; wrap 0xF -> 0x0
  cover property ($rose(!reset));
  cover property ($past(!reset) && !reset && $past(q)==4'hF && q==4'h0);
endmodule

// ---------- register_module SVA ----------
module register_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  d,
  input logic [7:0]  q
);
  default clocking cb @(posedge clk); endclocking

  // Synchronous reset drives 0x34 next cycle
  assert property (reset |=> q == 8'h34);

  // When not in reset, q captures prior-cycle d
  assert property ((!reset && $past(1'b1)) |-> q == $past(d));

  // No X/Z when not in reset
  assert property (!reset |-> !$isunknown(q));

  // Coverage: reset release; observe at least one data capture change
  cover property ($rose(!reset));
  cover property (!reset && $changed(q));
endmodule

// ---------- functional_module SVA (combinational equivalence) ----------
module functional_module_sva (
  input  logic [3:0] counter_in,
  input  logic [7:0] register_in,
  input  logic [7:0] final_out
);
  // Combinational sum, modulo 256
  always_comb
    assert (final_out == (register_in + {4'b0, counter_in}));

  // Optional: overflow coverage (carry out of bit 7)
  // Immediate cover via always_comb is not standard; rely on top-level cover below.
endmodule

// ---------- top_module SVA (connectivity + end-to-end) ----------
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  d,
  // Expose top-level outs and internal wires for integrity checks
  input  logic [3:0]  counter_out,
  input  logic [7:0]  register_out,
  input  logic [7:0]  final_out,
  input  logic [3:0]  counter_out_wire,
  input  logic [7:0]  register_out_wire,
  input  logic [7:0]  final_out_wire
);
  default clocking cb @(posedge clk); endclocking

  // Wiring integrity
  assert property (counter_out  == counter_out_wire);
  assert property (register_out == register_out_wire);
  assert property (final_out    == final_out_wire);

  // End-to-end functional check at clock edges (mod 256)
  assert property (final_out == (register_out + {4'b0, counter_out}));

  // Reset effect visible next cycle on all outs
  assert property (reset |=> (counter_out==4'd0 && register_out==8'h34
                              && final_out==8'h34));

  // No X/Z on top outputs when not in reset
  assert property (!reset |-> (!$isunknown(counter_out)
                            && !$isunknown(register_out)
                            && !$isunknown(final_out)));

  // Coverage: detect addition overflow at the top level
  cover property (!reset && (({1'b0,register_out} + {5'b0,counter_out})[8] == 1'b1));
endmodule

// ---------- Bind directives ----------
bind counter_module    counter_module_sva    u_counter_sva    (.clk(clk), .reset(reset), .q(q));
bind register_module   register_module_sva   u_register_sva   (.clk(clk), .reset(reset), .d(d), .q(q));
bind functional_module functional_module_sva u_functional_sva (.counter_in(counter_in), .register_in(register_in), .final_out(final_out));

// For top-level connectivity checks, bind where internal wires are visible
bind top_module top_module_sva u_top_sva (
  .clk(clk), .reset(reset), .d(d),
  .counter_out(counter_out), .register_out(register_out), .final_out(final_out),
  .counter_out_wire(counter_out_wire), .register_out_wire(register_out_wire), .final_out_wire(final_out_wire)
);