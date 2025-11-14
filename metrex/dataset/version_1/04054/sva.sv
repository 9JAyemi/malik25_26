// SVA checker for fifo. Bind this to the DUT.
// Focus: safety (no overflow/underflow), pointer/count/flag correctness,
// FIFO ordering, reset behavior, and key coverage.

module fifo_sva #(
  parameter int DEPTH = 8,
  parameter int WIDTH = 8,
  localparam int PTRW  = (DEPTH <= 2) ? 1 : $clog2(DEPTH)
)(
  input  logic                  clk,
  input  logic                  rst,

  // DUT IO
  input  logic [WIDTH-1:0]      data_in,
  input  logic                  wr_en,
  input  logic                  rd_en,
  input  logic [WIDTH-1:0]      data_out,
  input  logic                  full,
  input  logic                  empty,

  // DUT internal state (bound hierarchically)
  input  logic [PTRW-1:0]       wr_ptr,
  input  logic [PTRW-1:0]       rd_ptr,
  input  logic [PTRW-1:0]       count
);

  // Qualified transfers as observed at interface
  logic push, pop;
  always_comb begin
    push = wr_en && !full;
    pop  = rd_en && !empty;
  end

  // Shadow occupancy and data model (concise, reference-correct)
  int unsigned occ;
  bit [WIDTH-1:0] q[$];

  // Reset expectations
  property p_reset_state;
    @(posedge clk) rst |=> (wr_ptr==0 && rd_ptr==0 && count==0 && empty && !full);
  endproperty
  assert property (p_reset_state);

  // No illegal attempts (must not write when full w/o read, nor read when empty w/o write)
  assert property (@(posedge clk) disable iff (rst) (wr_en && !rd_en) |-> !full);
  assert property (@(posedge clk) disable iff (rst) (rd_en && !wr_en) |-> !empty);

  // Flags cannot be both set
  assert property (@(posedge clk) disable iff (rst) !(full && empty));

  // Pointer advance/hold rules (mod DEPTH)
  function automatic logic [PTRW-1:0] inc_mod(input logic [PTRW-1:0] v);
    inc_mod = (v == DEPTH-1) ? '0 : (v + 1'b1);
  endfunction

  assert property (@(posedge clk) disable iff (rst) push |=> wr_ptr == inc_mod($past(wr_ptr)));
  assert property (@(posedge clk) disable iff (rst) !push |=> wr_ptr == $past(wr_ptr));

  assert property (@(posedge clk) disable iff (rst) pop  |=> rd_ptr == inc_mod($past(rd_ptr)));
  assert property (@(posedge clk) disable iff (rst) !pop  |=> rd_ptr == $past(rd_ptr));

  // Reference occupancy model and flag equivalence
  // Model updates first, then compare DUT outputs to model
  always_ff @(posedge clk) begin
    if (rst) begin
      occ <= 0;
      q.delete();
    end else begin
      if (push) q.push_back(data_in);
      if (pop) begin
        bit [WIDTH-1:0] exp;
        if (q.size() == 0) begin
          // Should be unreachable due to 'pop' definition; keep concise
          exp = 'x;
        end else begin
          exp = q.pop_front();
          assert (data_out == exp)
            else $error("FIFO ordering/data mismatch: got %0h exp %0h", data_out, exp);
        end
      end
      // Occupancy update
      occ <= occ + (push ? 1 : 0) - (pop ? 1 : 0);
    end
  end

  // Occupancy range invariant
  assert property (@(posedge clk) disable iff (rst) (occ <= DEPTH));

  // DUT count and flags must match the reference model
  assert property (@(posedge clk) disable iff (rst) count == occ[PTRW-1:0]);
  assert property (@(posedge clk) disable iff (rst) full  == (occ == DEPTH));
  assert property (@(posedge clk) disable iff (rst) empty == (occ == 0));

  // Exact count next-state relation using interface visibility (redundant with model, but concise and strong)
  property p_count_next;
    @(posedge clk) disable iff (rst)
      1 |=> count == ($past(count)
                      + ($past(wr_en && !full) ? 1 : 0)
                      - ($past(rd_en && !empty) ? 1 : 0));
  endproperty
  assert property (p_count_next);

  // Coverage: reach full then empty, observe simultaneous push+pop, and pointer wrap
  cover property (@(posedge clk) disable iff (rst) empty ##1 push[*1:$] ##1 full ##1 pop[*1:$] ##1 empty);
  cover property (@(posedge clk) disable iff (rst) push && pop);
  cover property (@(posedge clk) disable iff (rst) ($past(wr_ptr)==DEPTH-1 && push) |=> wr_ptr==0);
  cover property (@(posedge clk) disable iff (rst) ($past(rd_ptr)==DEPTH-1 && pop)  |=> rd_ptr==0);

endmodule

// Bind into the DUT (connect internal regs by hierarchical ports)
bind fifo fifo_sva #(.DEPTH(DEPTH), .WIDTH(8)) u_fifo_sva (
  .clk      (clk),
  .rst      (rst),
  .data_in  (data_in),
  .wr_en    (wr_en),
  .rd_en    (rd_en),
  .data_out (data_out),
  .full     (full),
  .empty    (empty),
  .wr_ptr   (wr_ptr),
  .rd_ptr   (rd_ptr),
  .count    (count)
);