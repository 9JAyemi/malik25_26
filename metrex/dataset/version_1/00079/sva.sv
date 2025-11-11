// SVA for serial_rx — concise, quality-focused
// Bind-friendly module that references DUT internals

`ifndef SERIAL_RX_SVA_SV
`define SERIAL_RX_SVA_SV

module serial_rx_sva #(
  parameter int CLK_PER_BIT = 50,
  parameter int CTR_SIZE    = $clog2(CLK_PER_BIT)
)(
  input  logic                   clk,
  input  logic                   rst,
  input  logic                   rx,
  input  logic [7:0]             data,       // equals data_q in DUT
  input  logic                   new_data,   // equals new_data_q in DUT
  // internal DUT signals (connected by bind)
  input  logic [1:0]             state_q,
  input  logic [CTR_SIZE-1:0]    ctr_q,
  input  logic [2:0]             bit_ctr_q,
  input  logic                   rx_q
);

  // Match DUT encoding
  localparam int IDLE      = 2'd0;
  localparam int WAIT_HALF = 2'd1;
  localparam int WAIT_FULL = 2'd2;
  localparam int WAIT_HIGH = 2'd3;

  localparam int HALF = (CLK_PER_BIT >> 1);
  localparam int LAST = (CLK_PER_BIT - 1);

  // Elaboration-time checks
  initial begin
    assert (CLK_PER_BIT >= 2)
      else $error("CLK_PER_BIT must be >= 2");
    assert (CTR_SIZE == $clog2(CLK_PER_BIT))
      else $error("CTR_SIZE must equal $clog2(CLK_PER_BIT)");
    assert ($bits(state_q)   == 2);
    assert ($bits(bit_ctr_q) == 3);
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Basic sanity
  assert property (state_q inside {[IDLE:WAIT_HIGH]});
  assert property (rx_q == $past(rx));

  // IDLE behavior
  assert property (state_q==IDLE && rx_q==1 |=> state_q==IDLE);
  assert property (state_q==IDLE && rx_q==0 |=> state_q==WAIT_HALF);
  // After holding IDLE for 2 cycles, counters are 0
  assert property (state_q==IDLE && $past(state_q==IDLE) |-> (ctr_q==0 && bit_ctr_q==0));

  // WAIT_HALF counting and exit at HALF
  assert property (state_q==WAIT_HALF && (ctr_q != HALF)
                   |=> state_q==WAIT_HALF && ctr_q == $past(ctr_q)+1);
  assert property (state_q==WAIT_HALF && (ctr_q == HALF)
                   |=> state_q==WAIT_FULL && ctr_q == 0);

  // WAIT_FULL counting between samples
  assert property (state_q==WAIT_FULL && (ctr_q != LAST)
                   |=> state_q==WAIT_FULL && ctr_q == $past(ctr_q)+1 && $stable(bit_ctr_q) && $stable(data) && !new_data);

  // Sampling on full bit period (intermediate bits)
  assert property (state_q==WAIT_FULL && (ctr_q == LAST) && (bit_ctr_q != 3'd7)
                   |=> state_q==WAIT_FULL
                       && ctr_q == 0
                       && bit_ctr_q == $past(bit_ctr_q)+1
                       && data == { $past(rx_q), $past(data[7:1]) }
                       && !new_data);

  // Sampling on last bit -> WAIT_HIGH + pulse new_data, bit_ctr wraps to 0
  assert property (state_q==WAIT_FULL && (ctr_q == LAST) && (bit_ctr_q == 3'd7)
                   |=> state_q==WAIT_HIGH
                       && ctr_q == 0
                       && bit_ctr_q == 3'd0
                       && data == { $past(rx_q), $past(data[7:1]) }
                       && new_data);

  // WAIT_HIGH holds until line is high, then return to IDLE
  assert property (state_q==WAIT_HIGH && rx_q==0 |=> state_q==WAIT_HIGH);
  assert property (state_q==WAIT_HIGH && rx_q==1 |=> state_q==IDLE);

  // new_data pulse correctness and one-cycle width
  assert property (new_data |-> $past(state_q==WAIT_FULL && ctr_q==LAST && bit_ctr_q==3'd7));
  assert property (new_data |=> !new_data);

  // Data and bit_ctr only change on sample edges
  assert property (!$past(state_q==WAIT_FULL && ctr_q==LAST) |-> $stable(data));
  assert property (!$past(state_q==WAIT_FULL && ctr_q==LAST) |-> $stable(bit_ctr_q));

  // Counter stability in WAIT_HIGH
  assert property (state_q==WAIT_HIGH |=> $stable(ctr_q));

  // Coverage
  sequence s_sample; state_q==WAIT_FULL && ctr_q==LAST; endsequence
  cover property (state_q==IDLE ##1 state_q==WAIT_HALF ##1 state_q==WAIT_FULL ##1 state_q==WAIT_HIGH ##1 state_q==IDLE);
  cover property (s_sample[*8] ##1 (new_data && state_q==WAIT_HIGH) ##1 state_q==IDLE);

endmodule

// Bind to DUT (connects to internals by name)
bind serial_rx serial_rx_sva #(.CLK_PER_BIT(CLK_PER_BIT), .CTR_SIZE(CTR_SIZE)) serial_rx_sva_i (
  .clk      (clk),
  .rst      (rst),
  .rx       (rx),
  .data     (data),
  .new_data (new_data),
  .state_q  (state_q),
  .ctr_q    (ctr_q),
  .bit_ctr_q(bit_ctr_q),
  .rx_q     (rx_q)
);

`endif