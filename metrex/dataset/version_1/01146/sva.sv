// SVA checker for dualport_RAM
// - Uses a shadow byte-memory to check read data and stability
// - Enforces address range (addr <= 30) due to addr+1 usage
// - Checks single-operation priority chain and output stability
// - Provides compact functional coverage

module dualport_RAM_sva (
  input  logic        clk,
  input  logic [15:0] d_in_1,
  input  logic [15:0] d_out_1,
  input  logic [7:0]  addr_1,
  input  logic        rd_1,
  input  logic        wr_1,
  input  logic [15:0] d_in_2,
  input  logic [15:0] d_out_2,
  input  logic [7:0]  addr_2,
  input  logic        rd_2,
  input  logic        wr_2
);
  // Same edge as DUT
  default clocking cb @(negedge clk); endclocking

  // Priority-taken operations (mirror the DUT's if/else chain)
  wire take_r1 = rd_1;
  wire take_w1 = !rd_1 && wr_1;
  wire take_r2 = !rd_1 && !wr_1 && rd_2;
  wire take_w2 = !rd_1 && !wr_1 && !rd_2 && wr_2;

  // Shadow byte memory + validity map (avoid false fails on uninitialized reads)
  logic [7:0] mem_ref [0:31];
  logic       vld     [0:31];

  // Track past-valid for $stable
  bit past_v;
  always_ff @(negedge clk) past_v <= 1'b1;

  // Reference model updates (only on taken writes, and only for legal addresses)
  always_ff @(negedge clk) begin
    if (take_w1 && addr_1 <= 8'd30) begin
      mem_ref[addr_1]   <= d_in_1[7:0];
      mem_ref[addr_1+1] <= d_in_1[15:8];
      vld[addr_1]       <= 1'b1;
      vld[addr_1+1]     <= 1'b1;
    end else if (take_w2 && addr_2 <= 8'd30) begin
      mem_ref[addr_2]   <= d_in_2[7:0];
      mem_ref[addr_2+1] <= d_in_2[15:8];
      vld[addr_2]       <= 1'b1;
      vld[addr_2+1]     <= 1'b1;
    end
  end

  // Disable first cycle to avoid $past/$stable issues
  default disable iff (!past_v);

  // At most one operation can take per cycle (matches if/else chain)
  assert property ($onehot0({take_r1,take_w1,take_r2,take_w2}))
    else $error("Multiple operations taken in a single cycle");

  // Address range safety: addr+1 must be within [0:31] => addr <= 30
  assert property (take_r1 |-> addr_1 <= 8'd30)
    else $error("Port1 read addr out of range (>30)");
  assert property (take_w1 |-> addr_1 <= 8'd30)
    else $error("Port1 write addr out of range (>30)");
  assert property (take_r2 |-> addr_2 <= 8'd30)
    else $error("Port2 read addr out of range (>30)");
  assert property (take_w2 |-> addr_2 <= 8'd30)
    else $error("Port2 write addr out of range (>30)");

  // Read data correctness when bytes are known
  assert property (take_r1 && addr_1 <= 8'd30 && vld[addr_1] && vld[addr_1+1]
                   |-> d_out_1 == {mem_ref[addr_1+1], mem_ref[addr_1]})
    else $error("Port1 read data mismatch");
  assert property (take_r2 && addr_2 <= 8'd30 && vld[addr_2] && vld[addr_2+1]
                   |-> d_out_2 == {mem_ref[addr_2+1], mem_ref[addr_2]})
    else $error("Port2 read data mismatch");

  // Outputs only change on their own reads (writes or other-port ops must not change them)
  assert property (!take_r1 |-> $stable(d_out_1))
    else $error("d_out_1 changed without a Port1 read");
  assert property (!take_r2 |-> $stable(d_out_2))
    else $error("d_out_2 changed without a Port2 read");

  // Priority behavior coverage (exercise each branch and common contention cases)
  cover property (take_r1);
  cover property (take_w1);
  cover property (take_r2);
  cover property (take_w2);

  // Boundary address coverage
  cover property (take_r1 && addr_1 == 8'd30);
  cover property (take_w1 && addr_1 == 8'd30);
  cover property (take_r2 && addr_2 == 8'd30);
  cover property (take_w2 && addr_2 == 8'd30);

  // Contention scenarios to confirm priority
  cover property (rd_1 && rd_2 && take_r1);                       // r1 over r2
  cover property (!rd_1 && wr_1 && rd_2 && take_w1);              // w1 over r2
  cover property (rd_1 && wr_2 && take_r1);                       // r1 over w2
  cover property (!rd_1 && wr_1 && wr_2 && !rd_2 && take_w1);     // w1 over w2
endmodule

// Bind the checker to all instances of dualport_RAM
bind dualport_RAM dualport_RAM_sva sva_i (
  .clk,
  .d_in_1, .d_out_1, .addr_1, .rd_1, .wr_1,
  .d_in_2, .d_out_2, .addr_2, .rd_2, .wr_2
);