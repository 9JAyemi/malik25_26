// SVA checker for fifo
module fifo_sva #(
  parameter int depth = 8,
  parameter int data_width = 8
)(
  input  logic                       clk,
  input  logic                       reset,
  input  logic                       write_en,
  input  logic [data_width-1:0]      data_in,
  input  logic                       read_en,
  input  logic [data_width-1:0]      data_out,
  input  logic [$clog2(depth):0]     write_ptr,
  input  logic [$clog2(depth):0]     read_ptr,
  input  logic [$clog2(depth):0]     count
);

  // convenience signals
  wire push = write_en && (count < depth);
  wire pop  = read_en  && (count > 0);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // asynchronous reset behavior
  assert property (@(posedge reset) (write_ptr==0 && read_ptr==0 && count==0));

  // bounds
  assert property (count <= depth);
  assert property (push |-> (write_ptr < depth));
  assert property (pop  |-> (read_ptr  < depth));

  // ptr/count update rules
  assert property (push |-> write_ptr == $past(write_ptr)+1);
  assert property (!push |-> write_ptr == $past(write_ptr));
  assert property (pop  |-> read_ptr  == $past(read_ptr)+1);
  assert property (!pop |-> read_ptr  == $past(read_ptr));

  // count transitions (all four cases)
  assert property ( push && !pop |-> count == $past(count)+1 );
  assert property (!push &&  pop |-> count == $past(count)-1 );
  assert property ( push &&  pop |-> count == $past(count)    );
  assert property (!push && !pop |-> count == $past(count)    );

  // structural invariant (no wrap model): difference equals count
  assert property ((write_ptr - read_ptr) == count);

  // no overflow/underflow effects
  assert property ((write_en && count==depth) |-> $stable(write_ptr) && $stable(count));
  assert property ((read_en  && count==0   ) |-> $stable(read_ptr)  && $stable(count) && $stable(data_out));

  // data_out only updates on successful read
  assert property (!pop |-> $stable(data_out));

  // simple scoreboard to check FIFO order
  logic [data_width-1:0] q[$];
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      q.delete();
    end else begin
      if (pop) begin
        // model must not underflow
        assert(q.size()>0) else $error("FIFO model underflow");
        assert(data_out == q[0]) else $error("FIFO order mismatch");
        q.pop_front();
      end
      if (push) begin
        q.push_back(data_in);
      end
      // keep scoreboard size aligned with DUT count
      assert(q.size() == count) else $error("Model/DUT count mismatch");
    end
  end

  // coverage
  cover property (count==0 ##[1:$] count==depth ##[1:$] count==0);                 // fill then drain
  cover property (write_en && count==depth);                                       // overflow attempt
  cover property (read_en  && count==0);                                           // underflow attempt
  cover property (write_en && read_en && count>0 && count<depth);                  // simultaneous R/W
  cover property (push ##[1:$] pop);                                               // write then later read

endmodule

// Bind into DUT
bind fifo fifo_sva #(.depth(depth), .data_width(data_width)) fifo_sva_i (
  .clk      (clk),
  .reset    (reset),
  .write_en (write_en),
  .data_in  (data_in),
  .read_en  (read_en),
  .data_out (data_out),
  .write_ptr(write_ptr),
  .read_ptr (read_ptr),
  .count    (count)
);