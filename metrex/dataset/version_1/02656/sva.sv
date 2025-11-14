// SVA checker for module memory
module memory_sva #(
  parameter RD_DATA_WIDTH = 1,
  parameter RD_ADDR_WIDTH = 2,
  parameter MEM_DEPTH     = 4
)(
  input  logic                         rd_clk,
  input  logic                         reset,
  input  logic                         full,
  input  logic                         rd_en,
  input  logic [RD_ADDR_WIDTH-1:0]     rd_addr,
  input  logic [RD_DATA_WIDTH-1:0]     rd_data,
  input  logic [MEM_DEPTH-1:0]         remapping_memory,
  // tap internal storage via ref
  ref    logic [RD_DATA_WIDTH-1:0]     memory [0:MEM_DEPTH-1]
);

  // Static parameter sanity
  initial begin
    assert (MEM_DEPTH <= (1<<RD_ADDR_WIDTH))
      else $error("MEM_DEPTH (%0d) exceeds address space (%0d)", MEM_DEPTH, (1<<RD_ADDR_WIDTH));
    assert (RD_DATA_WIDTH >= 1)
      else $error("RD_DATA_WIDTH must be >= 1");
  end

  // Reset effects
  // rd_data cleared on reset edge and while reset is high on any rd_clk edge
  assert property (@(posedge reset) ##0 (rd_data == '0));
  assert property (@(posedge rd_clk) reset |-> ##0 (rd_data == '0));

  // Memory cleared on reset edge
  genvar gi_rst;
  generate
    for (genvar gi_rst = 0; gi_rst < MEM_DEPTH; gi_rst++) begin : G_RST_MEM
      assert property (@(posedge reset) ##0 (memory[gi_rst] == '0));
    end
  endgenerate

  // Remap behavior on full edge when not in reset
  generate
    for (genvar gi = 0; gi < MEM_DEPTH; gi++) begin : G_REMAP
      // On full with reset low, memory updates to replicated bit
      assert property (@(posedge full) disable iff (reset)
                       ##0 memory[gi] == {RD_DATA_WIDTH{remapping_memory[gi]}});
      // If full rises while reset is high, memory remains/sets to 0
      assert property (@(posedge full) reset |-> ##0 (memory[gi] == '0));
    end
  endgenerate

  // Read behavior: when rd_en, rd_data reflects memory[rd_addr] from same-cycle pre-state
  // Capture pre-NBA memory value to handle coincident full and rd_clk edges
  property p_read_data;
    logic [RD_DATA_WIDTH-1:0] m_pre;
    @(posedge rd_clk) disable iff (reset)
      (rd_en, m_pre = memory[rd_addr]) |-> ##0 (rd_data == m_pre);
  endproperty
  assert property (p_read_data);

  // If not enabled, rd_data holds its value across rd_clk edges (outside reset)
  assert property (@(posedge rd_clk) disable iff (reset) !rd_en |-> ##0 $stable(rd_data));

  // Address must be in range when used
  assert property (@(posedge rd_clk) disable iff (reset) rd_en |-> (rd_addr < MEM_DEPTH));

  // ------------- Functional coverage -------------

  // Reset observed
  cover property (@(posedge reset) 1);

  // Remap when not in reset
  cover property (@(posedge full) !reset);

  // Coincident full and read enable on rd_clk edge
  cover property (@(posedge rd_clk) rd_en && $rose(full));

  // Cover reads to each address
  generate
    for (genvar gc = 0; gc < MEM_DEPTH; gc++) begin : G_COV_ADDR
      cover property (@(posedge rd_clk) rd_en && (rd_addr == gc));
    end
  endgenerate

  // Cover remap writes of 0 and 1 for each location (only if RD_DATA_WIDTH >=1)
  generate
    for (genvar gw = 0; gw < MEM_DEPTH; gw++) begin : G_COV_WRITE_BITS
      cover property (@(posedge full) !reset && (remapping_memory[gw] == 1'b0));
      cover property (@(posedge full) !reset && (remapping_memory[gw] == 1'b1));
    end
  endgenerate

endmodule

// Bind into DUT
bind memory memory_sva #(
  .RD_DATA_WIDTH(RD_DATA_WIDTH),
  .RD_ADDR_WIDTH(RD_ADDR_WIDTH),
  .MEM_DEPTH    (MEM_DEPTH)
) u_memory_sva (
  .rd_clk            (rd_clk),
  .reset             (reset),
  .full              (full),
  .rd_en             (rd_en),
  .rd_addr           (rd_addr),
  .rd_data           (rd_data),
  .remapping_memory  (remapping_memory),
  .memory            (memory)
);