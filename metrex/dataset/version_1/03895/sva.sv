// SVA for chatgpt_generate_JC_counter
// Focused, high-value checks and concise functional coverage

module chatgpt_generate_JC_counter_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [31:0] Q,
  input  logic [31:0] lfsr_reg
);
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset takes effect immediately
  assert property (@(negedge rst_n) ##0 (lfsr_reg==32'h0000_0001 && Q==32'h0000_0001));

  // While in reset, hold reset values on clock edges
  assert property (@(posedge clk) !rst_n |-> (lfsr_reg==32'h0000_0001 && Q==32'h0000_0001));

  // LFSR next-state function
  assert property (disable iff (!rst_n)
    lfsr_reg == { $past(lfsr_reg[30:0]), ($past(lfsr_reg[31]) ^ $past(lfsr_reg[28])) }
  );

  // Q maps to previous cycle's lower nibble of lfsr_reg and is zero-extended
  assert property (disable iff (!rst_n)
    Q == { 28'h0, $past(lfsr_reg[3:0]) }
  );

  // Q upper bits must always be zero (including during reset)
  assert property (Q[31:4] == 28'h0);

  // No all-zero lockup state after reset is released
  assert property (disable iff (!rst_n) lfsr_reg != 32'h0);

  // No X/Z on state/output when out of reset; reset itself must be known
  assert property (@(posedge clk) !$isunknown(rst_n));
  assert property (disable iff (!rst_n) !$isunknown({lfsr_reg,Q}));

  // Functional coverage
  // 1) Observe reset deassertion and entry into running state
  cover property (@(posedge clk) !rst_n ##1 rst_n);

  // 2) See both feedback values occur (0 then 1) across steps
  cover property (disable iff (!rst_n)
    (($past(lfsr_reg[31]) ^ $past(lfsr_reg[28]))==1'b0) ##1
    (($past(lfsr_reg[31]) ^ $past(lfsr_reg[28]))==1'b1)
  );

  // 3) See multiple distinct nibble updates on Q
  cover property (disable iff (!rst_n) $changed(Q[3:0]) ##1 $changed(Q[3:0]) ##1 $changed(Q[3:0]));
endmodule

// Bind into DUT; lfsr_reg is internal and is connected hierarchically
bind chatgpt_generate_JC_counter
  chatgpt_generate_JC_counter_sva
    sva_i ( .clk(clk),
            .rst_n(rst_n),
            .Q(Q),
            .lfsr_reg(lfsr_reg) );