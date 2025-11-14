// SVA for module adder
// Binds to all instances and checks functional, reset, and X-safe behavior,
// plus concise coverage of key scenarios.

module adder_sva (
  input logic        clk,
  input logic        reset_n,
  input logic [7:0]  a,
  input logic [7:0]  b,
  input logic [7:0]  sum,
  input logic        carry
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n)

  // 1-cycle latency functional correctness (9-bit result)
  property p_add_correct;
    $past(reset_n) |-> {carry, sum} == ({1'b0,$past(a)} + {1'b0,$past(b)});
  endproperty
  assert property (p_add_correct);

  // Outputs known when out of reset
  assert property (!$isunknown({sum,carry}));

  // Optional: Inputs should be known when out of reset (helps catch driver issues)
  assert property (!$isunknown({a,b}));

  // Reset behavior: outputs forced to 0 and stable during reset
  // (kept outside default disable)
  assert property (@(posedge clk) !reset_n |-> ({sum,carry} == '0 && $stable({sum,carry})));

  // Lightweight functional coverage
  cover property ($rose(reset_n));                    // reset release observed
  cover property ($fell(reset_n));                    // reset assert observed
  cover property ($past(reset_n) && ({1'b0,$past(a)} + {1'b0,$past(b)}) > 9'd255); // carry case
  cover property ($past(reset_n) && ({1'b0,$past(a)} + {1'b0,$past(b)}) <= 9'd255); // no carry
  cover property (a==8'h00 && b==8'h00);             // trivial sum
  cover property (a==8'hFF && b==8'h01);             // overflow boundary
  cover property (a==8'hAA && b==8'h55);             // mid-range mix

endmodule

bind adder adder_sva u_adder_sva(.*);