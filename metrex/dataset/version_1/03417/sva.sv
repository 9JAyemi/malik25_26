// SVA for axis_srl_fifo
// Focus: handshake correctness, occupancy, pointer bounds/moves, data/tlast/tuser ordering, corner cases

module axis_srl_fifo_sva #(
  parameter int DEPTH = 4,
  parameter int DATA_WIDTH = 8
)(
  input  logic                     clk,
  input  logic                     rst,

  // DUT I/Os
  input  logic [DATA_WIDTH-1:0]    input_axis_tdata,
  input  logic                     input_axis_tvalid,
  input  logic                     input_axis_tlast,
  input  logic                     input_axis_tuser,
  input  logic                     input_axis_tready,

  input  logic                     output_axis_tready,
  input  logic [DATA_WIDTH-1:0]    output_axis_tdata,
  input  logic                     output_axis_tvalid,
  input  logic                     output_axis_tlast,
  input  logic                     output_axis_tuser,

  input  logic [2:0]               count,

  // Internals
  input  logic [2:0]               head,
  input  logic [2:0]               tail,
  input  logic [2:0]               count_reg
);

  // Helpers
  let push = (input_axis_tvalid && input_axis_tready);
  let pop  = (output_axis_tready && (count > 0));

  // Reset behavior
  assert property (@(posedge clk) rst |-> (head==0 && tail==0 && count==0 && !output_axis_tvalid && input_axis_tready));

  // Basic invariants
  assert property (@(posedge clk) disable iff (rst) count == count_reg);
  assert property (@(posedge clk) disable iff (rst) count <= DEPTH);
  assert property (@(posedge clk) disable iff (rst) input_axis_tready == (count < DEPTH));
  assert property (@(posedge clk) disable iff (rst) output_axis_tvalid == (output_axis_tready && (count > 0)));

  // No underflow/overflow handshakes
  assert property (@(posedge clk) disable iff (rst) !(count==0 && output_axis_tvalid));
  assert property (@(posedge clk) disable iff (rst) !(count==DEPTH && input_axis_tvalid && input_axis_tready));

  // Occupancy next-state model (should be exact for a well-formed FIFO)
  assert property (@(posedge clk) disable iff (rst)
                   1 |=> count == $past(count) + ($past(push)?1:0) - ($past(pop)?1:0));

  // Pointers stay within DEPTH range
  assert property (@(posedge clk) disable iff (rst) head < DEPTH);
  assert property (@(posedge clk) disable iff (rst) tail < DEPTH);

  // Head movement
  assert property (@(posedge clk) disable iff (rst)
                   $past(push) |-> head == (($past(head)==DEPTH-1) ? 3'd0 : $past(head)+3'd1));
  assert property (@(posedge clk) disable iff (rst)
                   !$past(push) |-> head == $past(head));

  // Tail movement
  assert property (@(posedge clk) disable iff (rst)
                   $past(pop) |-> tail == (($past(tail)==DEPTH-1) ? 3'd0 : $past(tail)+3'd1));
  assert property (@(posedge clk) disable iff (rst)
                   !$past(pop) |-> tail == $past(tail));

  // Output valid only on real pop, and no pop when empty
  assert property (@(posedge clk) disable iff (rst) output_axis_tvalid |-> pop);
  assert property (@(posedge clk) disable iff (rst) (count==0) |-> !pop);

  // Simple shadow-model to check FIFO data/tlast/tuser ordering
  logic [DATA_WIDTH-1:0] data_q[$];
  logic                  last_q[$];
  logic                  user_q[$];

  always_ff @(posedge clk) begin
    if (rst) begin
      data_q.delete(); last_q.delete(); user_q.delete();
    end else begin
      if (push) begin
        data_q.push_back(input_axis_tdata);
        last_q.push_back(input_axis_tlast);
        user_q.push_back(input_axis_tuser);
      end
      if (pop) begin
        // Model must not underflow
        assert (data_q.size()>0)
          else $error("Shadow-model underflow");
        if (data_q.size()>0) begin
          assert (output_axis_tdata == data_q[0])
            else $error("Data ordering mismatch");
          assert (output_axis_tlast == last_q[0])
            else $error("tlast ordering mismatch");
          assert (output_axis_tuser == user_q[0])
            else $error("tuser ordering mismatch");
          data_q.pop_front();
          last_q.pop_front();
          user_q.pop_front();
        end
      end
    end
  end

  // Coverage
  cover property (@(posedge clk) disable iff (rst) (count==0) ##1 push[*DEPTH] ##1 (count==DEPTH));
  cover property (@(posedge clk) disable iff (rst) (count==DEPTH) ##1 pop[*DEPTH] ##1 (count==0));
  cover property (@(posedge clk) disable iff (rst) (count>0 && count<DEPTH && push && pop));
  cover property (@(posedge clk) disable iff (rst) $past(head)==DEPTH-1 && $past(push) && head==0);
  cover property (@(posedge clk) disable iff (rst) $past(tail)==DEPTH-1 && $past(pop)  && tail==0);
  cover property (@(posedge clk) disable iff (rst) push ##[1:$] pop && output_axis_tlast);

endmodule

// Bind into DUT
bind axis_srl_fifo axis_srl_fifo_sva #(.DEPTH(DEPTH), .DATA_WIDTH(DATA_WIDTH))
  axis_srl_fifo_sva_i (
    .clk,
    .rst,
    .input_axis_tdata,
    .input_axis_tvalid,
    .input_axis_tlast,
    .input_axis_tuser,
    .input_axis_tready,
    .output_axis_tready,
    .output_axis_tdata,
    .output_axis_tvalid,
    .output_axis_tlast,
    .output_axis_tuser,
    .count,
    .head(head),
    .tail(tail),
    .count_reg(count_reg)
  );