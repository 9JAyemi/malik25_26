// SVA checker for HLS_accel_a_ram
`ifndef SYNTHESIS
module HLS_accel_a_ram_sva #(
  parameter int DWIDTH = 32,
  parameter int AWIDTH = 10,
  parameter int MEM_SIZE = 1024
) (
  input  logic                   clk,
  input  logic [AWIDTH-1:0]      addr0,
  input  logic                   ce0,
  input  logic [DWIDTH-1:0]      d0,
  input  logic                   we0,
  input  logic [DWIDTH-1:0]      q0,
  input  logic [AWIDTH-1:0]      addr1,
  input  logic                   ce1,
  input  logic [DWIDTH-1:0]      q1
);

  default clocking cb @(posedge clk); endclocking

  // Shadow model and valid map (only check reads after init via write)
  logic [DWIDTH-1:0] ref_mem [MEM_SIZE-1:0];
  logic              valid_mem [MEM_SIZE-1:0];

  // Past-valid guard to avoid time-0 artifacts
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Update shadow model on writes
  always_ff @(posedge clk) begin
    if (ce0 && we0 && !$isunknown(addr0)) begin
      ref_mem[addr0]  <= d0;
      valid_mem[addr0] <= 1'b1;
    end
  end

  // Basic control integrity
  assert property (past_valid |-> !$isunknown({ce0, ce1, we0}));

  // Address range when enabled
  assert property (past_valid && ce0 && !$isunknown(addr0) |-> addr0 < MEM_SIZE);
  assert property (past_valid && ce1 && !$isunknown(addr1) |-> addr1 < MEM_SIZE);

  // Outputs hold when CE deasserted
  assert property (past_valid && !ce0 |=> $stable(q0));
  assert property (past_valid && !ce1 |=> $stable(q1));

  // Port0 write-through behavior
  assert property (past_valid && ce0 && we0 |-> q0 == d0);

  // Port0 read returns pre-write memory value
  assert property (past_valid && ce0 && !we0 && !$isunknown(addr0) && valid_mem[addr0]
                   |-> q0 == ref_mem[addr0]);

  // Port1 read returns pre-write memory value (also covers write/read same-addr collision)
  assert property (past_valid && ce1 && !$isunknown(addr1) && valid_mem[addr1]
                   |-> q1 == ref_mem[addr1]);

  // Explicit same-addr write (p0) / read (p1) collision: p1 must see old data
  assert property (past_valid && ce0 && we0 && ce1 && (addr0==addr1) && valid_mem[addr1]
                   |-> q1 == ref_mem[addr1]);

  // Functional coverage
  cover property (ce0 && we0);                        // write
  cover property (ce0 && !we0);                       // port0 read
  cover property (ce1);                               // port1 read
  cover property (ce0 && we0 && ce1 && (addr0==addr1));  // same-addr write/read
  cover property (ce0 && we0 && ce1 && (addr0!=addr1));  // diff-addr concurrent
  cover property (ce0 && we0 ##1 ce0 && !we0 && addr0==$past(addr0)); // write then read same addr
  cover property (ce0 && we0 ##1 ce0 && we0 && addr0==$past(addr0));  // back-to-back writes same addr
endmodule

// Bind into all instances of HLS_accel_a_ram
bind HLS_accel_a_ram HLS_accel_a_ram_sva #(
  .DWIDTH(DWIDTH),
  .AWIDTH(AWIDTH),
  .MEM_SIZE(MEM_SIZE)
) ram_sva_bind (
  .clk  (clk),
  .addr0(addr0),
  .ce0  (ce0),
  .d0   (d0),
  .we0  (we0),
  .q0   (q0),
  .addr1(addr1),
  .ce1  (ce1),
  .q1   (q1)
);
`endif