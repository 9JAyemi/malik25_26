// SVA for fifo. Bind this file to fifo.
// Focuses on safety, flag/count/pointer relationships, protocol, and data integrity.

module fifo_sva #(
  parameter int DEPTH = 4096,
  parameter int WIDTH = 24,
  parameter int ADDR_WIDTH = $clog2(DEPTH)
)(
  input  logic                     clk,
  input  logic                     rst,
  input  logic                     wr_en,
  input  logic                     rd_en,
  input  logic [WIDTH-1:0]         din,
  input  logic [WIDTH-1:0]         dout,
  input  logic                     full,
  input  logic                     empty,
  input  logic [ADDR_WIDTH-1:0]    data_count,
  input  logic [ADDR_WIDTH-1:0]    wr_ptr,
  input  logic [ADDR_WIDTH-1:0]    rd_ptr
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  let wr_fire = wr_en && !full;
  let rd_fire = rd_en && !empty;

  // Reset state next cycle after rst
  assert property (rst |=> (wr_ptr==0 && rd_ptr==0 && data_count==0 && empty && !full));

  // Flag definitions and mutual exclusion
  assert property (empty == (wr_ptr == rd_ptr));
  assert property (full  == (wr_ptr == (rd_ptr + 1'b1)));
  assert property (!(full && empty));

  // Count bounds and equivalence to pointer distance (single-slot full scheme)
  assert property (data_count < DEPTH);
  assert property (data_count == (wr_ptr - rd_ptr));

  // Pointer step behavior
  assert property (wr_ptr == $past(wr_ptr) + ($past(wr_fire) ? 1 : 0));
  assert property (rd_ptr == $past(rd_ptr) + ($past(rd_fire) ? 1 : 0));

  // Count update behavior (simul R/W => net zero)
  assert property (data_count == $past(data_count)
                                 + ($past(wr_fire) ? 1 : 0)
                                 - ($past(rd_fire) ? 1 : 0));

  // Flag/count consistency
  assert property (empty == (data_count == '0));
  assert property (full  == (data_count == (DEPTH-1)));

  // Illegal ops do not change state
  assert property ($past(wr_en && full  && !rd_en) |-> (wr_ptr==$past(wr_ptr) && data_count==$past(data_count)));
  assert property ($past(rd_en && empty && !wr_en) |-> (rd_ptr==$past(rd_ptr) && data_count==$past(data_count)));

  // Simultaneous valid R/W keeps occupancy
  assert property ($past(wr_fire && rd_fire) |-> (data_count==$past(data_count)));

  // Data integrity: once written to an address, until that address is written again,
  // if that address is pointed by rd_ptr then dout must reflect that data.
  property p_mem_consistency;
    logic [ADDR_WIDTH-1:0] a;
    logic [WIDTH-1:0]      d;
    (wr_fire, a = wr_ptr, d = din)
      |-> (((rd_ptr == a) |-> (dout == d))
           until_with (wr_fire && (wr_ptr == a)));
  endproperty
  assert property (p_mem_consistency);

  // Basic covers
  cover property (empty ##1 wr_fire ##1 !empty);                     // leave empty
  cover property (!full ##1 wr_fire [* (DEPTH-1)] ##1 full);         // reach full from empty
  cover property (!empty ##1 rd_fire [*1:$] ##1 empty);              // drain to empty
  cover property (wr_fire && rd_fire);                               // simultaneous R/W
  cover property ($past(wr_ptr) == {ADDR_WIDTH{1'b1}} && wr_ptr==0); // wr_ptr wrap
  cover property ($past(rd_ptr) == {ADDR_WIDTH{1'b1}} && rd_ptr==0); // rd_ptr wrap

endmodule

bind fifo fifo_sva #(.DEPTH(DEPTH), .WIDTH(WIDTH), .ADDR_WIDTH(ADDR_WIDTH)) fifo_sva_i (
  .clk(clk),
  .rst(rst),
  .wr_en(wr_en),
  .rd_en(rd_en),
  .din(din),
  .dout(dout),
  .full(full),
  .empty(empty),
  .data_count(data_count),
  .wr_ptr(wr_ptr),
  .rd_ptr(rd_ptr)
);