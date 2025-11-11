// SVA for MemTextures
// Bind-only checker; no DUT/testbench changes required.

module MemTextures_sva;
  // Constants derived from DUT
  localparam int SPO_W    = 92;
  localparam int ADDR_W   = 8;
  localparam int DATA_W   = 32;
  localparam int CONCAT_W = ADDR_W + DATA_W;   // 40
  localparam int PAD_W    = SPO_W - CONCAT_W;  // 52

  default clocking cb @(posedge clk); endclocking

  // Make $past safe
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Functional check: 1-cycle registered, zero-extended {a, mem[a]}
  property p_spo_model;
    past_valid && !$isunknown($past({a, mem[a]}))
      |-> spo == {{PAD_W{1'b0}}, $past({a, mem[a]})};
  endproperty
  assert property (p_spo_model);

  // Upper padding bits must be zero (checked every cycle)
  assert property (@(posedge clk) spo[SPO_W-1:CONCAT_W] == '0);

  // X-propagation: when inputs are known, output must be known next cycle
  assert property (@(posedge clk)
    past_valid && !$isunknown($past({a, mem[a]})) |-> !$isunknown(spo));

  // Minimal functional coverage
  cover property (@(posedge clk) past_valid && a == 8'h00);
  cover property (@(posedge clk) past_valid && a == 8'hFF);
  cover property (@(posedge clk) past_valid && $past(a) != a);
  cover property (@(posedge clk) past_valid && $past(a) == a);
  cover property (@(posedge clk) past_valid && !$isunknown(mem[a]) && mem[a] != '0);
endmodule

bind MemTextures MemTextures_sva memtextures_sva_i();