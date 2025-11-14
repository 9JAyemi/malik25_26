// SVA bind module for fifo_buffer
module fifo_buffer_sva #(parameter int FIFO_SIZE = 16) (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        fifo_rd,
  input  logic        fifo_wr,
  input  logic [7:0]  fifo_data_in,
  input  logic        fifo_empty,
  input  logic        fifo_full,
  input  logic [7:0]  fifo_data_out,
  input  logic [3:0]  fifo_count,
  input  logic [3:0]  read_ptr,
  input  logic [3:0]  write_ptr,
  input  logic [3:0]  next_read_ptr,
  input  logic [3:0]  next_write_ptr
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Effective operations (as intended by flags)
  let eff_wr = fifo_wr && !fifo_full;
  let eff_rd = fifo_rd && !fifo_empty;

  // Reset state
  assert property (!rst_n |=> (fifo_count==0 && read_ptr==0 && write_ptr==0));

  // Flag decodes
  assert property (fifo_empty == (fifo_count==0));
  assert property (fifo_full  == (fifo_count==FIFO_SIZE));

  // Count never exceeds capacity
  assert property (fifo_count <= FIFO_SIZE);

  // No underflow/overflow on blocked ops
  assert property ((fifo_empty && fifo_rd && !fifo_wr) |-> $stable(fifo_count) && $stable(read_ptr));
  assert property ((fifo_full  && fifo_wr && !fifo_rd) |-> $stable(fifo_count) && $stable(write_ptr));

  // Count update matches effective operations
  assert property (fifo_count == $past(fifo_count) + (eff_wr?1:0) - (eff_rd?1:0));

  // Pointers advance exactly one (mod FIFO_SIZE) when the previous cycle had an effective op
  assert property ($past(eff_wr) |-> write_ptr == (($past(write_ptr)==FIFO_SIZE-1) ? 0 : $past(write_ptr)+1));
  assert property (!$past(eff_wr) |-> write_ptr == $past(write_ptr));
  assert property ($past(eff_rd) |-> read_ptr  == (($past(read_ptr)==FIFO_SIZE-1)  ? 0 : $past(read_ptr)+1));
  assert property (!$past(eff_rd) |-> read_ptr  == $past(read_ptr));

  // Any pointer change must be caused by the prior effective op
  assert property ((write_ptr != $past(write_ptr)) |-> $past(eff_wr));
  assert property ((read_ptr  != $past(read_ptr))  |-> $past(eff_rd));

  // Empty implies pointers equal (ring FIFO invariant)
  assert property ((fifo_count==0) |-> (read_ptr==write_ptr));

  // Data output changes only on effective read
  assert property (!(fifo_rd && !fifo_empty) |-> $stable(fifo_data_out));

  // Implementation coherence with next_* pipeline
  assert property (write_ptr == $past(next_write_ptr));
  assert property (read_ptr  == $past(next_read_ptr));

  // Lightweight scoreboard for data integrity and count consistency
  logic [7:0] model_q[$];
  logic [7:0] exp;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      model_q.delete();
    end else begin
      if (eff_wr) model_q.push_back(fifo_data_in);
      if (eff_rd) begin
        assert (model_q.size() > 0) else $error("Underflow: read when model empty");
        if (model_q.size() > 0) begin
          exp = model_q.pop_front();
          assert (fifo_data_out === exp)
            else $error("Data mismatch: exp=%0h got=%0h", exp, fifo_data_out);
        end
      end
      assert (fifo_count == model_q.size())
        else $error("Count mismatch: size=%0d count=%0d", model_q.size(), fifo_count);
    end
  end

  // Coverage
  cover property (eff_wr && eff_rd);                 // simultaneous read+write
  cover property (fifo_empty ##1 eff_wr ##1 !fifo_empty);
  cover property ((fifo_count==FIFO_SIZE-1) ##1 eff_wr ##1 fifo_full);
  cover property (fifo_empty ##1 (fifo_rd && !fifo_wr));  // attempted read on empty
  cover property (fifo_full  ##1 (fifo_wr && !fifo_rd));  // attempted write on full
  cover property (fifo_count==FIFO_SIZE);            // full condition reachable
endmodule

// Bind into DUT
bind fifo_buffer fifo_buffer_sva #(.FIFO_SIZE(FIFO_SIZE)) u_fifo_buffer_sva (
  .clk(clk),
  .rst_n(rst_n),
  .fifo_rd(fifo_rd),
  .fifo_wr(fifo_wr),
  .fifo_data_in(fifo_data_in),
  .fifo_empty(fifo_empty),
  .fifo_full(fifo_full),
  .fifo_data_out(fifo_data_out),
  .fifo_count(fifo_count),
  .read_ptr(read_ptr),
  .write_ptr(write_ptr),
  .next_read_ptr(next_read_ptr),
  .next_write_ptr(next_write_ptr)
);