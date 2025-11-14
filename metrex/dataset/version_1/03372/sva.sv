// SVA checkers and binds for i2c_master and i2c_slave

// ---------------------------
// i2c_master SVA
// ---------------------------
module i2c_master_sva (
  input  logic        SCL,
  input  logic        SDA_OUT,
  input  logic        SDA_IN,
  input  logic        SDA_OUT_EN,
  input  logic        SDA_IN_EN,
  input  logic        ACK,
  input  logic [2:0]  state,
  input  logic [7:0]  data_out
);
  default clocking cb @(posedge SCL); endclocking
  logic past_v; always_ff @(posedge SCL) past_v <= 1'b1;
  default disable iff (!past_v);

  // State well-formed
  a_state_range:     assert property (state inside {[3'd0:3'd6]});
  a_no_x_state:      assert property (!$isunknown(state));

  // Encodings
  a_sda_out_en:      assert property (SDA_OUT_EN == (state inside {3'd1,3'd2,3'd4}));
  a_sda_in_en:       assert property (SDA_IN_EN  == (state inside {3'd2,3'd3,3'd5}));
  a_ack_val:         assert property (ACK == ((state inside {3'd3,3'd5}) ? ~SDA_IN : 1'b1));

  // Transitions
  a_idle_hold:       assert property ((state==3'd0 && SDA_OUT!=1'b0) |=> state==3'd0);
  a_idle_to_start:   assert property ((state==3'd0 && SDA_OUT==1'b0) |=> (state==3'd1 && data_out==8'hA0));
  a_start_to_addr:   assert property (state==3'd1 |=> state==3'd2);
  a_addr_ack:        assert property ((state==3'd2 && ACK==1'b0) |=> state==3'd3);
  a_addr_nack_hold:  assert property ((state==3'd2 && ACK!=1'b0) |=> state==3'd2);
  a_data_ack:        assert property ((state==3'd3 && ACK==1'b0) |=> (state==3'd4 && data_out==8'hC0));
  a_data_nack_hold:  assert property ((state==3'd3 && ACK!=1'b0) |=> state==3'd3);
  a_rs_to_recv:      assert property (state==3'd4 |=> state==3'd5);
  a_recv_ack:        assert property ((state==3'd5 && ACK==1'b0) |=> state==3'd6);
  a_recv_nack_hold:  assert property ((state==3'd5 && ACK!=1'b0) |=> state==3'd5);
  a_stop_to_idle:    assert property (state==3'd6 |=> state==3'd0);

  // data_out only updates at defined points, otherwise holds
  a_data_out_stable: assert property (
                        !($past(state)==3'd0 && $past(SDA_OUT)==1'b0) &&
                        !($past(state)==3'd3 && $past(ACK)==1'b0)
                        |=> data_out==$past(data_out)
                      );

  // Coverage: full master transaction
  c_full_txn: cover property (
    (state==3'd0 && SDA_OUT==1'b0)
    ##1 (state==3'd1)
    ##1 (state==3'd2) ##1 (ACK==1'b0, state==3'd3)
    ##1 (ACK==1'b0, state==3'd4)
    ##1 (state==3'd5) ##1 (ACK==1'b0, state==3'd6)
    ##1 (state==3'd0)
  );

  // Coverage: NACK holds in address/data/receive
  c_addr_nack_hold:  cover property ((state==3'd2 && ACK!=1'b0) ##1 (state==3'd2));
  c_data_nack_hold:  cover property ((state==3'd3 && ACK!=1'b0) ##1 (state==3'd3));
  c_recv_nack_hold:  cover property ((state==3'd5 && ACK!=1'b0) ##1 (state==3'd5));
endmodule

bind i2c_master i2c_master_sva
(
  .SCL(SCL),
  .SDA_OUT(SDA_OUT),
  .SDA_IN(SDA_IN),
  .SDA_OUT_EN(SDA_OUT_EN),
  .SDA_IN_EN(SDA_IN_EN),
  .ACK(ACK),
  .state(state),
  .data_out(data_out)
);

// ---------------------------
// i2c_slave SVA
// ---------------------------
module i2c_slave_sva (
  input  logic        SCL,
  input  logic        SDA_IN,
  input  logic        SDA_OUT,
  input  logic        SDA_OUT_EN,
  input  logic        SDA_IN_EN,
  input  logic        ACK,
  input  logic [2:0]  state,
  input  logic [7:0]  data_in
);
  default clocking cb @(posedge SCL); endclocking
  logic past_v; always_ff @(posedge SCL) past_v <= 1'b1;
  default disable iff (!past_v);

  // State well-formed
  a_state_range:     assert property (state inside {[3'd0:3'd5]});
  a_no_x_state:      assert property (!$isunknown(state));

  // Encodings
  a_sda_out_en:      assert property (SDA_OUT_EN == (state inside {3'd2,3'd4}));
  a_sda_out_value:   assert property (SDA_OUT == data_in[7]);

  // Transitions
  a_idle_hold:       assert property ((state==3'd0 && SDA_IN!=1'b0) |=> state==3'd0);
  a_idle_to_start:   assert property ((state==3'd0 && SDA_IN==1'b0) |=> state==3'd1);
  a_start_to_addr:   assert property (state==3'd1 |=> state==3'd2);
  a_addr_ack:        assert property ((state==3'd2 && ACK==1'b0) |=> state==3'd3);
  a_addr_nack_hold:  assert property ((state==3'd2 && ACK!=1'b0) |=> state==3'd2);
  a_data_ack:        assert property ((state==3'd3 && ACK==1'b0) |=> state==3'd4);
  a_data_nack_hold:  assert property ((state==3'd3 && ACK!=1'b0) |=> state==3'd3);
  a_send_to_stop:    assert property (state==3'd4 |=> state==3'd5);
  a_stop_to_idle:    assert property (state==3'd5 |=> state==3'd0);

  // Shift behavior
  a_shift_when_en:   assert property (SDA_IN_EN |=> data_in == { $past(data_in[6:0]), $past(SDA_IN) });
  a_hold_when_dis:   assert property (!SDA_IN_EN |=> data_in == $past(data_in));

  // Coverage: full slave transaction
  c_full_rx_tx: cover property (
    (state==3'd0 && SDA_IN==1'b0)
    ##1 (state==3'd1)
    ##1 (state==3'd2) ##1 (ACK==1'b0, state==3'd3)
    ##1 (ACK==1'b0, state==3'd4)
    ##1 (state==3'd5) ##1 (state==3'd0)
  );

  // Coverage: NACK holds in address/data
  c_addr_nack_hold:  cover property ((state==3'd2 && ACK!=1'b0) ##1 (state==3'd2));
  c_data_nack_hold:  cover property ((state==3'd3 && ACK!=1'b0) ##1 (state==3'd3));
endmodule

bind i2c_slave i2c_slave_sva
(
  .SCL(SCL),
  .SDA_IN(SDA_IN),
  .SDA_OUT(SDA_OUT),
  .SDA_OUT_EN(SDA_OUT_EN),
  .SDA_IN_EN(SDA_IN_EN),
  .ACK(ACK),
  .state(state),
  .data_in(data_in)
);