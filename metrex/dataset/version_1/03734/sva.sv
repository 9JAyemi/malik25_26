// SVA for nfa_accept_samples_generic_hw_start_indices_ram
// Focus: write-first behavior, read data correctness, address range, q0 stability, basic X-checks, and concise coverage.
// Place in a separate file and compile with the DUT. Uses bind; no DUT edits required.

// synopsys translate_off

module nfa_accept_samples_generic_hw_start_indices_ram_sva #(
  parameter int DWIDTH   = 32,
  parameter int AWIDTH   = 4,
  parameter int MEM_SIZE = 16
)(
  input logic                 clk,
  input logic                 ce0,
  input logic                 we0,
  input logic [AWIDTH-1:0]    addr0,
  input logic [DWIDTH-1:0]    d0,
  input logic [DWIDTH-1:0]    q0
);
  // Simple golden model and validity tracking
  logic [DWIDTH-1:0] model_ram [MEM_SIZE];
  logic [MEM_SIZE-1:0] valid;
  bit seen_clk;

  initial begin
    valid   = '0;
    seen_clk = 1'b0;
  end

  always_ff @(posedge clk) begin
    seen_clk <= 1'b1;
    if (ce0 && we0) begin
      model_ram[addr0] <= d0;
      valid[addr0]     <= 1'b1;
    end
  end

  default clocking cb @(posedge clk); endclocking

  // Address must be in range whenever enabled
  assert property (disable iff (!seen_clk)
                   ce0 |-> (addr0 < MEM_SIZE))
    else $error("Address out of range: %0d >= %0d", addr0, MEM_SIZE);

  // Write-first: write returns d0 on q0 next cycle
  assert property (disable iff (!seen_clk)
                   (ce0 && we0) |=> (q0 == $past(d0)))
    else $error("Write-first violation: q0 != d0");

  // Read returns the last written data (only enforce if written before)
  assert property (disable iff (!seen_clk)
                   (ce0 && !we0 && valid[addr0]) |=> (q0 == $past(model_ram[addr0])))
    else $error("Read data mismatch vs model");

  // When ce0 is low, q0 must hold its value
  assert property (disable iff (!seen_clk)
                   (!ce0) |=> (q0 == $past(q0)))
    else $error("q0 changed without ce0");

  // Any change on q0 must be due to ce0 in the previous cycle
  assert property (disable iff (!seen_clk)
                   $changed(q0) |-> $past(ce0))
    else $error("q0 changed without enable");

  // No-X on write data; and no-X on read data when address valid
  assert property (disable iff (!seen_clk)
                   (ce0 && we0) |-> !$isunknown(d0))
    else $error("d0 contains X/Z on write");
  assert property (disable iff (!seen_clk)
                   (ce0 && !we0 && valid[addr0]) |=> !$isunknown(q0))
    else $error("q0 contains X/Z on read of valid entry");

  // Concise functional coverage
  cover property (ce0 && we0);                         // any write
  cover property (ce0 && !we0);                        // any read
  cover property (ce0 && we0 && (addr0 == '0));        // write to lowest addr
  cover property (ce0 && we0 && (addr0 == MEM_SIZE-1)); // write to highest addr
  cover property ((ce0 && we0) ##1 (ce0 && !we0 && (addr0 == $past(addr0)))); // write then read same addr
  cover property ((ce0 && we0) ##1 (ce0 && we0  && (addr0 == $past(addr0)))); // back-to-back writes same addr
  cover property (!ce0);                               // idle/hold

endmodule

// Bind into the RAM
bind nfa_accept_samples_generic_hw_start_indices_ram
  nfa_accept_samples_generic_hw_start_indices_ram_sva #(
    .DWIDTH(DWIDTH),
    .AWIDTH(AWIDTH),
    .MEM_SIZE(MEM_SIZE)
  ) ram_sva_bind (
    .clk  (clk),
    .ce0  (ce0),
    .we0  (we0),
    .addr0(addr0),
    .d0   (d0),
    .q0   (q0)
  );

// Optional lightweight wrapper-level coverage (reset activity and basic ops)
module nfa_accept_samples_generic_hw_start_indices_sva (
  input logic clk,
  input logic reset,
  input logic ce0,
  input logic we0
);
  default clocking cb @(posedge clk); endclocking
  cover property (reset);
  cover property ($fell(reset));
  cover property ($rose(ce0 && we0));
  cover property ($rose(ce0 && !we0));
endmodule

bind nfa_accept_samples_generic_hw_start_indices
  nfa_accept_samples_generic_hw_start_indices_sva wrapper_sva_bind (
    .clk  (clk),
    .reset(reset),
    .ce0  (ce0),
    .we0  (we0)
  );

// synopsys translate_on