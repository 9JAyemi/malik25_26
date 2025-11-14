// SVA checker for fifo_memory
module fifo_memory_sva #(
  parameter int SIZE   = 8,
  parameter int WIDTH  = 8,
  parameter int PTR_W  = $clog2(SIZE)
)(
  input  logic                  clk,
  input  logic                  wr_en,
  input  logic                  rd_en,
  input  logic [WIDTH-1:0]      data_in,
  input  logic                  empty,
  input  logic                  full,
  input  logic [WIDTH-1:0]      data_out,
  input  logic [PTR_W-1:0]      head,
  input  logic [PTR_W-1:0]      tail,
  input  logic [PTR_W-1:0]      next_head,
  input  logic [PTR_W-1:0]      next_tail
);

  localparam int SIZE_M1 = SIZE-1;

  function automatic logic [PTR_W-1:0] inc(input logic [PTR_W-1:0] p);
    inc = (p == SIZE_M1) ? '0 : (p + 1'b1);
  endfunction

  function automatic int unsigned diff(input logic [PTR_W-1:0] a, b);
    diff = (a >= b) ? int'(a - b) : int'(a + SIZE - b);
  endfunction

  default clocking cb @(posedge clk); endclocking

  // Lightweight scoreboard for ordering and occupancy
  logic                  synced;
  int unsigned           occ;
  logic [WIDTH-1:0]      sb[$];

  always_ff @(posedge clk) begin
    if (empty && (head == tail)) begin
      sb.delete();
      occ    = 0;
      synced <= 1'b1;
    end else if (synced) begin
      // Read first (pre-write data visibility), then write
      if (rd_en && !empty) begin
        if (sb.size() > 0) begin
          automatic logic [WIDTH-1:0] exp = sb[0];
          sb.pop_front();
          assert (data_out == exp)
            else $error("FIFO data mismatch: got %0h exp %0h", data_out, exp);
        end else begin
          assert (0) else $error("Read observed while scoreboard empty");
        end
      end
      if (wr_en && !full) sb.push_back(data_in);
      occ = sb.size();
    end
  end

  // Structural invariants
  assert property (next_tail == inc(tail));
  assert property (next_head == inc(head));
  assert property (empty == (head == tail));
  assert property (full  == ((inc(tail) == head) && (head != tail)));
  assert property (!(empty && full));

  // Pointer update rules
  assert property ((wr_en && !full)  |-> tail == inc($past(tail)));
  assert property (!(wr_en && !full) |-> tail == $past(tail));
  assert property ((rd_en && !empty)  |-> head == inc($past(head)));
  assert property (!(rd_en && !empty) |-> head == $past(head));

  // Data_out stability when no successful read
  assert property (!(rd_en && !empty) |-> data_out == $past(data_out));

  // Illegal op no-ops
  assert property ((wr_en && full)  |-> tail == $past(tail));
  assert property ((rd_en && empty) |-> head == $past(head) && data_out == $past(data_out));

  // Occupancy/model checks after first observed empty (sync point)
  assert property (synced |-> occ inside {[0:SIZE-1]});
  assert property (synced |-> (empty == (occ == 0)));
  assert property (synced |-> (full  == (occ == SIZE-1)));
  assert property (synced |-> occ == diff(tail, head));

  // Boundary transitions
  assert property ($past(full)  && rd_en && !wr_en |-> !full);
  assert property ($past(empty) && wr_en && !rd_en |-> !empty);

  // Coverage
  cover property (wr_en && !full);
  cover property (rd_en && !empty);
  cover property (wr_en && rd_en && !empty && !full);
  cover property (synced && occ == SIZE-1);
  cover property (synced && occ == 0);
  cover property (synced ##1 (tail == '0 && $past(tail) == SIZE_M1));
  cover property (synced ##1 (head == '0 && $past(head) == SIZE_M1));
  cover property (wr_en && full);
  cover property (rd_en && empty);

endmodule

// Bind into the DUT (connects to internal regs)
bind fifo_memory fifo_memory_sva #(
  .SIZE(SIZE), .WIDTH(8), .PTR_W(3)
) fifo_memory_sva_i (
  .clk(clk),
  .wr_en(wr_en),
  .rd_en(rd_en),
  .data_in(data_in),
  .empty(empty),
  .full(full),
  .data_out(data_out),
  .head(head),
  .tail(tail),
  .next_head(next_head),
  .next_tail(next_tail)
);