// SVA for deserializer. Bind into DUT.
// Focus: state machine legality/ordering, bit collection/counting, received protocol, resets, and compact coverage.

module deserializer_sva #(parameter int WIDTH = 8) (
  input  logic                  clk,
  input  logic                  rst,
  input  logic                  rxd,
  input  logic [WIDTH-1:0]      data,
  input  logic                  received,

  // tap DUT internals via bind
  input  logic [1:0]            state,
  input  logic [7:0]            bit_index,
  input  logic [WIDTH-1:0]      data_buf,
  input  logic                  received_buf
);
  // mirror DUT encodings
  localparam logic [1:0] S0 = 2'b00;
  localparam logic [1:0] S1 = 2'b01;
  localparam logic [1:0] S2 = 2'b11;
  localparam logic [1:0] S3 = 2'b10;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Structural ties
  a_data_tie:     assert property (data == data_buf);
  a_recv_tie:     assert property (received == received_buf);

  // No X after reset deassert
  a_known:        assert property (!$isunknown({state, bit_index, data_buf, received})));

  // Legal state encoding
  a_state_legal:  assert property (state inside {S0,S1,S2,S3});

  // Bit index bounds
  a_bi_bounds:    assert property (bit_index <= WIDTH);

  // Start behavior
  a_start_idle_hold: assert property (state==S0 && !rxd |=> state==S0);
  a_start_to_s1:     assert property (state==S0 && rxd  |=> state==S1 && bit_index==0);

  // Collect phase: increment and stay in S1 while collecting
  a_s1_inc:       assert property (state==S1 && bit_index < WIDTH
                                   |=> state==S1 && bit_index == $past(bit_index)+1);
  // Sample correctness
  a_sample:       assert property (state==S1 && bit_index < WIDTH
                                   |=> data_buf[$past(bit_index)] == $past(rxd));

  // Completion transition
  a_s1_done:      assert property (state==S1 && bit_index == WIDTH
                                   |=> state==S2 && received);

  // S2 then S3 with stability
  a_s2_step:      assert property (state==S2 |=> state==S3 && received
                                              && $stable(bit_index) && $stable(data_buf));
  // Cleanup in S3
  a_s3_cleanup:   assert property (state==S3 |=> state==S0
                                              && bit_index==0
                                              && data_buf=={WIDTH{1'b0}}
                                              && !received);

  // Received validity and pulse length
  a_recv_state:   assert property (received |-> (state inside {S2,S3}) && bit_index==WIDTH);
  a_recv_len2:    assert property ($rose(received) |-> received ##1 received ##1 !received);

  // Optional latency from start to received rise (WIDTH+1 cycles after entering S1)
  a_latency:      assert property (state==S0 && rxd |=> ##(WIDTH+1) $rose(received));

  // Reset behavior (not disabled)
  a_reset_clear:  assert property (@(posedge clk) rst
                                   |=> state==S0 && bit_index==0
                                       && data_buf=={WIDTH{1'b0}} && !received);

  // Compact coverage
  sequence collect_width_bits;
    (state==S1 && bit_index < WIDTH)[*WIDTH];
  endsequence

  c_full_frame: cover property (
    state==S0 && rxd
    ##1 collect_width_bits
    ##1 state==S2 && received
    ##1 state==S3 && received
    ##1 state==S0 && !received
  );

  c_idle:        cover property ((state==S0 && !rxd)[*5]);

  c_reset_mid:   cover property (state==S1 && bit_index inside {[1:WIDTH-1]}
                                 ##1 rst ##1 state==S0 && bit_index==0);
endmodule

// Bind into DUT; connects internals for checking
bind deserializer deserializer_sva #(.WIDTH(WIDTH)) i_deserializer_sva (
  .clk(clk),
  .rst(rst),
  .rxd(rxd),
  .data(data),
  .received(received),
  .state(state),
  .bit_index(bit_index),
  .data_buf(data_buf),
  .received_buf(received_buf)
);