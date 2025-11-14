// SVA checker for chatgpt_generate_RAM
// Focus: functional correctness across dual clocks, range/X checks, and concise coverage.

module chatgpt_generate_RAM_sva #(
  parameter ADDR_W = 8,
  parameter DATA_W = 4,
  parameter DEPTH  = 8
)(
  input  logic                  read_clk,
  input  logic                  write_clk,
  input  logic                  rst_n,
  input  logic                  write_en,
  input  logic [ADDR_W-1:0]     write_addr,
  input  logic [DATA_W-1:0]     write_data,
  input  logic                  read_en,
  input  logic [ADDR_W-1:0]     read_addr,
  input  logic [DATA_W-1:0]     read_data
);

  // Minimal reference model that mirrors DUT write semantics (writes use previous write_addr)
  logic [DATA_W-1:0] model_mem [0:DEPTH-1];
  logic [ADDR_W-1:0] prev_addr;

  initial begin
    integer i;
    for (i = 0; i < DEPTH; i++) model_mem[i] = '0;
    prev_addr = '0;
  end

  always_ff @(posedge write_clk) begin
    if (!rst_n) begin
      prev_addr <= '0;
    end else if (write_en) begin
      if (prev_addr < DEPTH) model_mem[prev_addr] <= write_data; // mirrors DUT write index
      prev_addr <= write_addr;
    end
  end

  // ---------------- Assertions ----------------

  // X-checks on inputs when sampled
  assert property (@(posedge write_clk) !$isunknown({rst_n, write_en, write_addr, write_data}));
  assert property (@(posedge read_clk)  !$isunknown({read_en, read_addr}));

  // Address range checks on actual access points
  assert property (@(posedge write_clk) disable iff (!rst_n)
                   write_en |-> (prev_addr < DEPTH))
    else $error("Write index (prev_addr) out of range: %0d", prev_addr);

  assert property (@(posedge read_clk) disable iff (!rst_n)
                   read_en |-> (read_addr < DEPTH))
    else $error("Read address out of range: %0d", read_addr);

  // Read data must update only when read_en; otherwise it must hold its value
  assert property (@(posedge read_clk) disable iff (!rst_n)
                   !read_en |-> $stable(read_data));

  assert property (@(posedge read_clk) disable iff (!rst_n)
                   $changed(read_data) |-> read_en);

  // Functional correctness vs model: synchronous read returns model value when enabled
  assert property (@(posedge read_clk) disable iff (!rst_n)
                   read_en && (read_addr < DEPTH) |-> (read_data == model_mem[read_addr]));

  // No X on read_data when a valid read is performed
  assert property (@(posedge read_clk) disable iff (!rst_n)
                   read_en && (read_addr < DEPTH) |-> !$isunknown(read_data));

  // ---------------- Coverage ----------------

  // Cover that each address is written (actual write index) and read
  genvar a;
  generate
    for (a = 0; a < DEPTH; a++) begin : C_ADDRS
      cover property (@(posedge write_clk) disable iff (!rst_n)
                      write_en && (prev_addr == a));
      cover property (@(posedge read_clk) disable iff (!rst_n)
                      read_en && (read_addr == a));
    end
  endgenerate

  // Back-to-back writes (to exercise write_addr pipeline effect)
  cover property (@(posedge write_clk) disable iff (!rst_n)
                  write_en ##1 write_en);

  // Write-then-read same address with expected data across clocks
  property p_wr_then_rd_same_data;
    logic [ADDR_W-1:0] a;
    logic [DATA_W-1:0] d;
    @(posedge write_clk) disable iff (!rst_n)
      (write_en && (prev_addr < DEPTH), a = prev_addr, d = write_data)
      ##[1:$] @(posedge read_clk)
      (read_en && (read_addr == a) && (read_data == d));
  endproperty
  cover property (p_wr_then_rd_same_data);

  // First write after reset uses address 0 (due to prev_addr reset)
  cover property (@(posedge write_clk)
                  !rst_n ##1 rst_n ##[1:$] write_en && (prev_addr == '0));

endmodule

// Bind into the DUT
bind chatgpt_generate_RAM chatgpt_generate_RAM_sva sva_inst (
  .read_clk  (read_clk),
  .write_clk (write_clk),
  .rst_n     (rst_n),
  .write_en  (write_en),
  .write_addr(write_addr),
  .write_data(write_data),
  .read_en   (read_en),
  .read_addr (read_addr),
  .read_data (read_data)
);