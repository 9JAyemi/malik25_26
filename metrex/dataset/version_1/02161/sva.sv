// Bindable SVA checker for pcie_data_receiver
module pcie_data_receiver_sva #(
  parameter int BUFFER_SIZE = 16,
  parameter int PTR_W       = $clog2(BUFFER_SIZE)  // should be 4 for BUFFER_SIZE=16
)(
  input  logic                  clk,
  input  logic                  rst,

  // DUT pins
  input  logic                  rx,
  input  logic                  rx_valid,
  input  logic                  rx_ready,
  input  logic                  rx_ack,
  input  logic                  tx,
  input  logic                  tx_valid,
  input  logic                  tx_ready,
  input  logic                  tx_ack,   // unused by DUT but ported for completeness

  // DUT internals (bind to these)
  input  logic [PTR_W-1:0]      head,
  input  logic [PTR_W-1:0]      tail,
  input  logic [PTR_W-1:0]      count
);

  // basic infrastructure
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  logic past_valid;
  always_ff @(posedge clk) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  function automatic int dist(input int h, input int t);
    return (h>=t) ? (h-t) : (h + BUFFER_SIZE - t);
  endfunction

  // Reset state
  assert property (rst |-> (head==0 && tail==0 && count==0 && rx_ready==0));

  // Ready/Valid/Ack relations (registered one cycle later in RTL)
  assert property (past_valid |-> rx_ready == $past(count < BUFFER_SIZE));
  assert property (past_valid |-> rx_ack   == $past(rx_valid && rx_ready));
  assert property (past_valid |-> tx_valid == ($past(tx_ready) && ($past(count) > 0)));

  // Count range safety
  assert property (count <= BUFFER_SIZE-1);

  // Count update must be +push -pop (will flag last-assignment bug and overflow)
  // push at t: rx_valid && rx_ready; pop at t: tx_ready && (count>0)
  assert property (past_valid |-> count ==
                   $past(count)
                   + (($past(rx_valid) && $past(rx_ready)) ? 1 : 0)
                   - (($past(tx_ready) && ($past(count)>0)) ? 1 : 0));

  // Head pointer update on push
  assert property (past_valid && $past(rx_valid && rx_ready)
                   |-> head == (($past(head)==BUFFER_SIZE-1) ? '0 : $past(head)+1));
  assert property (past_valid && !$past(rx_valid && rx_ready)
                   |-> head == $past(head));

  // Tail pointer update on pop
  assert property (past_valid && ($past(tx_ready) && ($past(count)>0))
                   |-> tail == (($past(tail)==BUFFER_SIZE-1) ? '0 : $past(tail)+1));
  assert property (past_valid && !($past(tx_ready) && ($past(count)>0))
                   |-> tail == $past(tail));

  // Distance(head,tail) must match count (catches mismatches on simultaneous push+pop)
  assert property (dist(head, tail) == count);

  // tx_valid implies previous-cycle tx_ready
  assert property (tx_valid |-> $past(tx_ready));

  // Scoreboard: data ordering and integrity (rx->FIFO->tx)
  bit q[$]; // queue of bits (rx/tx are 1-bit in DUT)
  always_ff @(posedge clk) begin
    if (rst) begin
      q.delete();
    end else begin
      if (rx_valid && rx_ready) q.push_back(rx);
      if (tx_valid) begin
        assert (q.size() > 0) else $error("Scoreboard underflow on tx_valid");
        if (q.size() > 0) begin
          assert (tx === q[0]) else $error("TX data mismatch: exp=%0b got=%0b", q[0], tx);
          q.pop_front();
        end
      end
    end
  end

  // Functional coverage
  cover property (rx_valid && rx_ready);                 // push
  cover property (tx_ready && (count>0));                // pop decision
  cover property ((rx_valid && rx_ready) && (tx_ready && (count>0))); // push+pop same cycle
  cover property ($past(head)==BUFFER_SIZE-1 && $past(rx_valid && rx_ready) && head==0); // head wrap
  cover property ($past(tail)==BUFFER_SIZE-1 && $past(tx_ready && ($past(count)>0)) && tail==0); // tail wrap
  cover property (count==0);
  cover property (count==BUFFER_SIZE-1);

endmodule

// Example bind (place in a testbench or a package):
// bind pcie_data_receiver
//   pcie_data_receiver_sva #(.BUFFER_SIZE(BUFFER_SIZE)) u_pcie_data_receiver_sva (
//     .clk(clk), .rst(rst),
//     .rx(rx), .rx_valid(rx_valid), .rx_ready(rx_ready), .rx_ack(rx_ack),
//     .tx(tx), .tx_valid(tx_valid), .tx_ready(tx_ready), .tx_ack(tx_ack),
//     .head(head), .tail(tail), .count(count)
//   );