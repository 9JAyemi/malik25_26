// SVA checker for SRAM_1R1W_BE
// Focus: functional correctness, byte enables, address ranges, data stability, hazards, and useful coverage.

module SRAM_1R1W_BE_sva #(
  parameter int ADDR_SZ = 9,
  parameter int DATA_SZ_BYTES = 8,
  parameter int MEM_SZ = 512
)(
  input  logic                         clk,
  input  logic                         write_en,
  input  logic [DATA_SZ_BYTES-1:0]     write_bytes,
  input  logic [ADDR_SZ-1:0]           write_addr,
  input  logic [(DATA_SZ_BYTES*8)-1:0] write_data,
  input  logic                         read_en,
  input  logic [ADDR_SZ-1:0]           read_addr,
  input  logic [(DATA_SZ_BYTES*8)-1:0] read_data
);

  localparam int W = DATA_SZ_BYTES*8;

  // Parameter sanity
  initial begin
    assert (MEM_SZ > 0) else $error("MEM_SZ must be > 0");
    assert (MEM_SZ <= (1<<ADDR_SZ)) else $error("ADDR_SZ too small for MEM_SZ");
  end

  default clocking cb @(posedge clk); endclocking

  // Shadow model (matches DUT semantics incl. RW same-cycle returns old data)
  logic [W-1:0] ref_mem [MEM_SZ-1:0];
  logic [W-1:0] ref_read_data;

  // init flag for $past
  logic init;
  always_ff @(posedge clk) init <= 1'b1;

  // Update reference
  int b;
  always_ff @(posedge clk) begin
    if (write_en) begin
      for (b = 0; b < DATA_SZ_BYTES; b++) begin
        if (write_bytes[b]) ref_mem[write_addr][b*8 +: 8] <= write_data[b*8 +: 8];
      end
    end
    if (read_en) begin
      ref_read_data <= ref_mem[read_addr];
    end
  end

  // Known/valid controls and addressing
  assert property (!$isunknown({write_en, read_en})); // enables known
  assert property (write_en |-> (!$isunknown(write_addr) && write_addr < MEM_SZ));
  assert property (read_en  |-> (!$isunknown(read_addr)  && read_addr  < MEM_SZ));
  assert property (write_en |-> !$isunknown(write_bytes));
  for (genvar i = 0; i < DATA_SZ_BYTES; i++) begin : g_x_wdata
    assert property (write_en && write_bytes[i] |-> !$isunknown(write_data[i*8 +: 8]));
  end

  // Functional correctness: read data equals reference (allowing X in uninitialized reads)
  assert property (read_en |-> ##0 (read_data === ref_read_data));

  // Read hold behavior when read_en=0
  assert property (disable iff (!init) !read_en |-> ##0 (read_data === $past(read_data)));

  // Any change on read_data must be due to read_en in prior cycle
  assert property (disable iff (!init) ##0 $changed(read_data) |-> $past(read_en));

  // Same-cycle read/write to same address returns old memory contents
  assert property (read_en && write_en && (read_addr == write_addr)
                   |-> ##0 (read_data === $past(ref_mem[read_addr])));

  // Coverage: exercise key scenarios concisely
  // Any write/read
  cover property (write_en);
  cover property (read_en);

  // Read-only and write-only cycles
  cover property (read_en && !write_en);
  cover property (write_en && !read_en);

  // All-bytes write and single-byte writes
  cover property (write_en && write_bytes == {DATA_SZ_BYTES{1'b1}});
  for (genvar j = 0; j < DATA_SZ_BYTES; j++) begin : g_cov_single_be
    cover property (write_en && (write_bytes == ({{(DATA_SZ_BYTES){1'b0}}} | (1'b1 << j))));
  end

  // Same-cycle RW same address hazard
  cover property (read_en && write_en && (read_addr == write_addr));

  // Boundary addresses (write and read)
  cover property (write_en && write_addr == '0);
  cover property (write_en && write_addr == MEM_SZ-1);
  cover property (read_en  && read_addr  == '0);
  cover property (read_en  && read_addr  == MEM_SZ-1);

  // Write then later read same address (any latency)
  property p_wr_then_rd;
    logic [ADDR_SZ-1:0] a;
    (write_en, a = write_addr) |-> ##[1:$] (read_en && read_addr == a);
  endproperty
  cover property (p_wr_then_rd);

  // Back-to-back reads to different addresses
  cover property (read_en ##1 read_en && (read_addr != $past(read_addr)));

endmodule

// Bind to all instances of DUT (parameters propagate)
bind SRAM_1R1W_BE
  SRAM_1R1W_BE_sva #(.ADDR_SZ(ADDR_SZ), .DATA_SZ_BYTES(DATA_SZ_BYTES), .MEM_SZ(MEM_SZ))
  SRAM_1R1W_BE_sva_i (
    .clk,
    .write_en,
    .write_bytes,
    .write_addr,
    .write_data,
    .read_en,
    .read_addr,
    .read_data
  );