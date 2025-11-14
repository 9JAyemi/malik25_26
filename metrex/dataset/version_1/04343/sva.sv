// SVA checker for fifo_memory_generator
// Focus: pointer semantics, data integrity, and useful coverage

`ifdef SVA

module fifo_memory_generator_chk #(
  parameter WIDTH      = 94,
  parameter DEPTH      = 64,
  parameter ADDR_WIDTH = $clog2(DEPTH),
  parameter MEM_WIDTH  = WIDTH + ADDR_WIDTH,
  parameter MEM_DEPTH  = DEPTH + 1
)(
  input  logic                   clk,
  input  logic                   wr_en,
  input  logic                   rd_en,
  input  logic [WIDTH-1:0]       din,
  input  logic [WIDTH-1:0]       dout,
  input  logic [ADDR_WIDTH-1:0]  wr_ptr,
  input  logic [ADDR_WIDTH-1:0]  rd_ptr,
  input  logic [ADDR_WIDTH-1:0]  next_wr_ptr,
  input  logic [ADDR_WIDTH-1:0]  next_rd_ptr,
  input  logic [MEM_WIDTH-1:0]   rd_data
);

  default clocking cb @(posedge clk); endclocking

  // Lightweight scoreboard to check data integrity
  logic [WIDTH-1:0] model_data   [0:DEPTH-1];
  bit               model_vld    [0:DEPTH-1];

  always_ff @(posedge clk) begin
    if (wr_en) begin
      model_data[wr_ptr] <= din;
      model_vld [wr_ptr] <= 1'b1;
    end
  end

  // Pointer next-state update rules
  assert property (wr_en  |=> next_wr_ptr == $past(wr_ptr) + 1);
  assert property (!wr_en |=> next_wr_ptr == $past(next_wr_ptr));

  assert property (rd_en  |=> next_rd_ptr == $past(rd_ptr) + 1);
  assert property (!rd_en |=> next_rd_ptr == $past(next_rd_ptr));

  // Pointers follow their next_* one cycle later
  assert property (wr_ptr == $past(next_wr_ptr));
  assert property (rd_ptr == $past(next_rd_ptr));

  // Read data must come from MSBs of rd_data (detects slicing bugs)
  assert property (rd_en |-> dout == rd_data[MEM_WIDTH-1:ADDR_WIDTH]);

  // dout updates only on read enable
  assert property (!rd_en |=> $stable(dout));

  // Scoreboard cross-check: when we've written that address before, read must match
  assert property (rd_en && model_vld[rd_ptr] |-> dout == model_data[rd_ptr]);

  // Useful coverage
  // Simultaneous read and write
  cover property (wr_en && rd_en);

  // Read after write to same address (1-cycle distance)
  cover property (wr_en ##1 (rd_en && (rd_ptr == $past(wr_ptr))));

  // Pointer wrap-around on write and read
  cover property (wr_en && (wr_ptr == DEPTH-1) ##1 wr_en && (wr_ptr == 0));
  cover property (rd_en && (rd_ptr == DEPTH-1) ##1 rd_en && (rd_ptr == 0));

endmodule

// Bind to DUT
bind fifo_memory_generator fifo_memory_generator_chk #(
  .WIDTH(WIDTH),
  .DEPTH(DEPTH),
  .ADDR_WIDTH(ADDR_WIDTH),
  .MEM_WIDTH(MEM_WIDTH),
  .MEM_DEPTH(MEM_DEPTH)
) u_fifo_memory_generator_chk (
  .clk        (clk),
  .wr_en      (wr_en),
  .rd_en      (rd_en),
  .din        (din),
  .dout       (dout),
  .wr_ptr     (wr_ptr),
  .rd_ptr     (rd_ptr),
  .next_wr_ptr(next_wr_ptr),
  .next_rd_ptr(next_rd_ptr),
  .rd_data    (rd_data)
);

`endif