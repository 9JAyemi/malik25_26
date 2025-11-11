// SVA for uartcon_tx
// Bind this module to uartcon_tx
module uartcon_tx_sva
(
  input rst_n,
  input clk,
  input txd,
  input valid,
  input load,
  input [7:0] data,

  // internal DUT signals
  input [1:0] sample_count,
  input [2:0] bit_count,
  input [7:0] tx_data,
  input       sample_point,
  input [3:0] state,
  input       out_data
);

  // Mirror DUT encodings
  localparam S_IDLE  = 4'd0;
  localparam S_START = 4'd1;
  localparam S_DATA  = 4'd2;
  localparam S_STOP  = 4'd3;
  localparam S_LAST  = 4'd4;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Reset/post-reset sanity
  a_reset_post: assert property ($rose(rst_n) |=> state==S_IDLE && sample_count==2'd0 && bit_count==3'd0 && txd==1'b1 && load==1'b0);

  // sample_count behavior and sample_point definition
  a_sc_idle:    assert property ($past(state)==S_IDLE |-> sample_count==2'd0);
  a_sc_active:  assert property ($past(state)!=S_IDLE |-> (($past(sample_count)!=2'd3 && sample_count==$past(sample_count)+1) ||
                                                           ($past(sample_count)==2'd3 && sample_count==2'd0)));
  a_sp_def:     assert property (sample_point == (sample_count==2'd3));
  a_sp_active:  assert property (sample_point |-> state!=S_IDLE);

  // bit_count behavior
  a_bc_reset:   assert property ($past(state)!=S_DATA |-> bit_count==3'd0);
  a_bc_hold:    assert property ($past(state)==S_DATA && !$past(sample_point) |-> bit_count==$past(bit_count));
  a_bc_inc:     assert property ($past(state)==S_DATA && $past(sample_point) && $past(bit_count)!=3'd7 |-> bit_count==$past(bit_count)+1);
  a_bc_wrap:    assert property ($past(state)==S_DATA && $past(sample_point) && $past(bit_count)==3'd7 |-> bit_count==3'd0);

  // Shifter correctness (on sample point)
  a_shift:      assert property ($past(state)==S_DATA && $past(sample_point) |-> tx_data == {1'b0, $past(tx_data[7:1])});

  // FSM transitions (complete and exclusive)
  a_idle_v:     assert property ($past(state)==S_IDLE && $past(valid) |-> state==S_START && load && tx_data==$past(data));
  a_idle_hold:  assert property ($past(state)==S_IDLE && !$past(valid) |-> state==S_IDLE);

  a_start_hold: assert property ($past(state)==S_START && !$past(sample_point) |-> state==S_START);
  a_start_next: assert property ($past(state)==S_START &&  $past(sample_point) |-> state==S_DATA);

  a_data_hold:  assert property ($past(state)==S_DATA && (!$past(sample_point) || ($past(sample_point)&&$past(bit_count)!=3'd7)) |-> state==S_DATA);
  a_data_next:  assert property ($past(state)==S_DATA &&  $past(sample_point) && $past(bit_count)==3'd7 |-> state==S_STOP);

  a_stop_hold:  assert property ($past(state)==S_STOP && !$past(sample_point) |-> state==S_STOP);
  a_stop_next:  assert property ($past(state)==S_STOP &&  $past(sample_point) |-> state==S_LAST);

  a_last_hold:  assert property ($past(state)==S_LAST && !$past(sample_point) |-> state==S_LAST);
  a_last_next:  assert property ($past(state)==S_LAST &&  $past(sample_point) |-> state==S_IDLE);

  // Outputs and datapath
  a_txd_map:    assert property (txd==out_data);
  a_idle_hi:    assert property (state==S_IDLE  |-> out_data==1'b1);
  a_start_lo:   assert property (state==S_START |-> out_data==1'b0);
  a_stop_hi:    assert property (state==S_STOP  |-> out_data==1'b1);
  a_last_hi:    assert property (state==S_LAST  |-> out_data==1'b1);
  a_data_bit:   assert property (state==S_DATA  |-> out_data==tx_data[0]);

  // Load pulse is one-cycle and only sourced by IDLE+valid
  a_load_src:   assert property (load |-> $past(state)==S_IDLE && $past(valid));
  a_load_len:   assert property ($past(load) |-> !load);

  // Stop entry condition must be on last data bit sample
  a_stop_entry: assert property ($past(state)==S_DATA && state==S_STOP |-> $past(sample_point) && $past(bit_count)==3'd7);

  // Minimal covers
  c_full_frame: cover property ($past(state)==S_IDLE && $past(valid) ##1
                                state==S_START ##[1:$]
                                state==S_DATA  ##[1:$]
                                state==S_STOP  ##[1:$]
                                state==S_LAST  ##[1:$]
                                state==S_IDLE);

  sequence sp_in_data; state==S_DATA && sample_point; endsequence
  c_8bits:      cover property (sp_in_data [->8] ##1 state==S_STOP);

endmodule

bind uartcon_tx uartcon_tx_sva sva (
  .rst_n(rst_n),
  .clk(clk),
  .txd(txd),
  .valid(valid),
  .load(load),
  .data(data),
  .sample_count(sample_count),
  .bit_count(bit_count),
  .tx_data(tx_data),
  .sample_point(sample_point),
  .state(state),
  .out_data(out_data)
);