// SVA checker for fifo. Bind this module to fifo as shown below.
module fifo_sva #(
  parameter DATA_WIDTH = 8,
  parameter ADDR_WIDTH = 8
)(
  input  logic                       clk,
  input  logic                       rst,
  // DUT ports
  input  logic                       enqueue,
  input  logic                       dequeue,
  input  logic [DATA_WIDTH-1:0]      data_i,
  input  logic [DATA_WIDTH-1:0]      data_o,
  input  logic [ADDR_WIDTH:0]        count,
  input  logic                       empty,
  input  logic                       full,
  // DUT internals (bound)
  input  logic [ADDR_WIDTH-1:0]      enqueue_ptr,
  input  logic [ADDR_WIDTH-1:0]      dequeue_ptr,
  input  logic                       w_enqueue,
  input  logic                       w_dequeue,
  input  logic [DATA_WIDTH-1:0]      w_data_o
);

  localparam int DEPTH = (1 << ADDR_WIDTH);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Basic sanity / range
  assert property (!$isunknown({empty,full,count,enqueue_ptr,dequeue_ptr,w_enqueue,w_dequeue,data_o})));
  assert property (count <= DEPTH);
  assert property (empty == (count == 0));
  assert property (full  == (count == DEPTH));

  // Reset effects (synchronous)
  assert property (rst |-> (count == 0 && enqueue_ptr == '0 && dequeue_ptr == '0));

  // Gating of effective ops
  assert property (full  |-> (w_enqueue == 1'b0));
  assert property (!full |-> (w_enqueue == enqueue));
  assert property (empty |-> (w_dequeue == 1'b0));
  assert property (!empty |-> (w_dequeue == dequeue));

  // No under/overflow preconditions
  assert property (w_enqueue |-> $past(count) < DEPTH);
  assert property (w_dequeue |-> $past(count) > 0);

  // Count update semantics
  assert property ((w_enqueue == w_dequeue) |-> count == $past(count));
  assert property (( w_enqueue && !w_dequeue) |-> count == $past(count) + 1);
  assert property ((!w_enqueue &&  w_dequeue) |-> count == $past(count) - 1);

  // Pointer update + wrap-around
  assert property (!w_enqueue |-> enqueue_ptr == $past(enqueue_ptr));
  assert property (!w_dequeue |-> dequeue_ptr == $past(dequeue_ptr));

  assert property (w_enqueue && ($past(enqueue_ptr) != DEPTH-1) |-> enqueue_ptr == $past(enqueue_ptr) + 1);
  assert property (w_enqueue && ($past(enqueue_ptr) == DEPTH-1) |-> enqueue_ptr == '0);

  assert property (w_dequeue && ($past(dequeue_ptr) != DEPTH-1) |-> dequeue_ptr == $past(dequeue_ptr) + 1);
  assert property (w_dequeue && ($past(dequeue_ptr) == DEPTH-1) |-> dequeue_ptr == '0);

  // Output muxing behavior
  assert property (!empty |-> data_o == w_data_o);
  assert property (empty && (enqueue && dequeue) |-> data_o == data_i);
  assert property (empty && !(enqueue && dequeue) |-> data_o == {DATA_WIDTH{1'b0}});

  // Lightweight functional scoreboard for data ordering
  typedef logic [DATA_WIDTH-1:0] data_t;
  data_t q[$];

  // Track and check FIFO contents
  always @(posedge clk) begin
    if (rst) begin
      q = {};
    end else begin
      logic enq = w_enqueue;
      logic deq = w_dequeue;
      data_t di = data_i;
      data_t front = (q.size() > 0) ? q[0] : '0;

      // Special empty + enqueue + dequeue case: pass-through and only enqueue internally
      if (empty && enqueue && dequeue) begin
        assert (data_o == data_i);
        q.push_back(di);
      end else begin
        // Check read data when dequeuing or just peeking
        if (deq) begin
          assert (q.size() > 0);
          assert (data_o == front);
        end else if (!empty) begin
          assert (data_o == front);
        end
        // Update model after checks: pop then push (order matters for simultaneous ops)
        if (deq) q.pop_front();
        if (enq) q.push_back(di);
      end

      // Model-DUT consistency
      assert (q.size() == count);
      assert ((q.size() == 0) == empty);
      assert ((q.size() == DEPTH) == full);
      assert (q.size() <= DEPTH);
    end
  end

  // Coverage
  cover property ($rose(full));
  cover property ($rose(empty));
  cover property (empty && enqueue && dequeue);                 // pass-through case
  cover property (!empty && !full && enqueue && dequeue);       // mid-queue simultaneous
  cover property (full && enqueue && dequeue);                  // drop enqueue, allow dequeue
  cover property (w_enqueue && $past(enqueue_ptr) == DEPTH-1);  // write pointer wrap
  cover property (w_dequeue && $past(dequeue_ptr) == DEPTH-1);  // read pointer wrap

endmodule

// Bind into the DUT to get access to internal nets/regs
bind fifo fifo_sva #(.DATA_WIDTH(DATA_WIDTH), .ADDR_WIDTH(ADDR_WIDTH)) u_fifo_sva (
  .clk(clk),
  .rst(rst),
  .enqueue(enqueue),
  .dequeue(dequeue),
  .data_i(data_i),
  .data_o(data_o),
  .count(count),
  .empty(empty),
  .full(full),
  .enqueue_ptr(enqueue_ptr),
  .dequeue_ptr(dequeue_ptr),
  .w_enqueue(w_enqueue),
  .w_dequeue(w_dequeue),
  .w_data_o(w_data_o)
);