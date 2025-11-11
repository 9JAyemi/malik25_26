// SVA for top_module and submodules. Bind into DUT; no TB code required.

// Top-level SVA (uses internal nets via bind with .*)
module top_module_sva (
  input logic         clk,
  input logic         reset,
  input logic [15:0]  in,
  input logic [7:0]   out_hi,
  input logic [7:0]   out_lo,
  input logic [7:0]   out,
  input logic [7:0]   hi_reg,
  input logic [7:0]   lo_reg,
  input logic [7:0]   out_reg
);
  default clocking cb @(posedge clk); endclocking

  // Combinational pass-throughs and final function consistency
  always_comb begin
    assert (out_hi == hi_reg);
    assert (out_lo == lo_reg);
    assert (out    == out_reg);
    assert (out    == (out_hi | out_lo));
  end

  // Asynchronous reset behavior visible at top (flip_flop q drives out_lo)
  // Reset drives q=0 immediately on reset edge and at every clk while reset is 1
  assert property (@(posedge reset) 1 |-> ##0 (out_lo == 8'h00));
  assert property (@(posedge clk)   reset |-> ##0 (out_lo == 8'h00));

  // Functional timing of inverter FF: on clk, when not in reset, q = ~d (d = in[7:0])
  assert property (@(posedge clk) !reset |-> ##0 (out_lo == ~ $past(in[7:0])));

  // Sanity: outputs not X/Z on clock edges
  assert property (@(posedge clk) !$isunknown({out_hi, out_lo, out}));

  // End-to-end coverages
  cover property (@(posedge reset) 1);                         // async reset asserted
  cover property (@(posedge clk) $past(reset) && !reset);      // reset deasserted between clocks
  cover property (@(posedge clk) !reset && in[7:0]==8'h00 ##1 out_lo==8'hFF);
  cover property (@(posedge clk) !reset && in[7:0]==8'hFF ##1 out_lo==8'h00);
  cover property (@(posedge clk) in[15:8]==8'h00 && out_hi==8'h00);
  cover property (@(posedge clk) in[15:8]==8'hFF && out_hi==8'hFF);
  cover property (@(posedge clk) !reset && (out_hi!=8'h00) && (out_lo!=8'h00) && (out==(out_hi|out_lo)));
endmodule

bind top_module top_module_sva top_module_sva_i(.*);


// Barrel shifter SVA: pure-slice combinational correctness
module barrel_shifter_sva (
  input logic [15:0] in,
  input logic [7:0]  out
);
  always_comb assert (out == in[15:8]);
  cover property (1'b1); // simple instantiation coverage
endmodule

bind barrel_shifter barrel_shifter_sva bs_sva_i(.*);


// Inverting async-reset FF SVA
module flip_flop_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  d,
  input  logic [7:0]  q
);
  // Immediate zero on async reset edge; hold zero while reset high
  assert property (@(posedge reset) 1 |-> ##0 (q == 8'h00));
  assert property (@(posedge clk)   reset |-> ##0 (q == 8'h00));

  // On clock when not reset, capture inverted d (observe q after NBA)
  assert property (@(posedge clk) !reset |-> ##0 (q == ~ $past(d)));

  // No X on q at clock edges
  assert property (@(posedge clk) !$isunknown(q));

  // Coverage
  cover property (@(posedge clk) !reset && d==8'h00 ##1 q==8'hFF);
  cover property (@(posedge clk) !reset && d==8'hFF ##1 q==8'h00);
endmodule

bind flip_flop flip_flop_sva ff_sva_i(.*);


// OR functional module SVA
module functional_module_sva (
  input logic [7:0] in1,
  input logic [7:0] in2,
  input logic [7:0] out
);
  always_comb assert (out == (in1 | in2));
  cover property ((in1!=8'h00) && (in2!=8'h00) && (out==(in1|in2)));
endmodule

bind functional_module functional_module_sva fm_sva_i(.*);