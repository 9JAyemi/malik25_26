// SVA for ps2. Bind this file to the DUT.
// Focus: FSM legality, sequencing, counters, data capture, parity behavior, and key functional coverage.

module ps2_sva (
  input  logic        CLKOUT,
  input  logic        Rx,
  input  logic        Tx,
  input  logic [8:0]  data_bits,
  input  logic        parity_bit,
  input  logic        start_bit_detected,
  input  logic [3:0]  bit_count,
  input  logic [1:0]  state
);
  // Mirror DUT encodings
  localparam logic [1:0] IDLE       = 2'b00;
  localparam logic [1:0] START_BIT  = 2'b01;
  localparam logic [1:0] DATA_BITS  = 2'b10;
  localparam logic [1:0] PARITY_BIT = 2'b11;

  default clocking cb @(posedge CLKOUT); endclocking

  // Basic sanity
  a_no_x:        assert property ( !$isunknown({state, bit_count, Tx}) );
  a_state_legal: assert property ( state inside {IDLE, START_BIT, DATA_BITS, PARITY_BIT} );
  a_cnt_range:   assert property ( bit_count <= 4'd7 );

  // IDLE behavior and start detection
  a_idle_tx1:    assert property ( state==IDLE |-> Tx==1'b1 );
  a_idle_hold:   assert property ( state==IDLE && Rx!=1'b0 |=> state==IDLE );
  a_idle_to_start:
    assert property ( state==IDLE && Rx==1'b0 |=> state==START_BIT && bit_count==0 && start_bit_detected==1 );

  // START_BIT behavior
  a_start_tx0:   assert property ( state==START_BIT |-> Tx==1'b0 );
  a_start_from_idle:
    assert property ( state==START_BIT |-> $past(state)==IDLE );
  // Bit capture: the bit at index (bit_count at START_BIT) equals prior Rx on the next cycle
  a_start_capture:
    assert property ( state==START_BIT |=> data_bits[$past(bit_count)] == $past(Rx) );
  // Normal progression (reachable path): from START_BIT to DATA_BITS and increment count
  a_start_prog:
    assert property ( state==START_BIT && $past(bit_count)!=4'd7
                      |=> state==DATA_BITS && bit_count==$past(bit_count)+1 );

  // DATA_BITS behavior
  a_data_tx_matches:
    assert property ( state==DATA_BITS |-> Tx == data_bits[bit_count] );
  a_data_inc:
    assert property ( state==DATA_BITS && bit_count!=4'd7
                      |=> state==DATA_BITS && bit_count==$past(bit_count)+1 );
  a_data_to_parity:
    assert property ( state==DATA_BITS && bit_count==4'd7
                      |=> state==PARITY_BIT && bit_count==0 );

  // PARITY behavior and update
  a_parity_tx:
    assert property ( state==PARITY_BIT |-> Tx == ~parity_bit );
  a_parity_to_idle:
    assert property ( state==PARITY_BIT |=> state==IDLE );
  a_parity_update_when_flag:
    assert property ( state==PARITY_BIT && start_bit_detected==1
                      |=> parity_bit == ^$past(data_bits) && start_bit_detected==0 );
  a_parity_stable_when_no_flag:
    assert property ( state==PARITY_BIT && start_bit_detected==0
                      |=> parity_bit == $past(parity_bit) && start_bit_detected==0 );

  // Start flag discipline
  a_startflag_rise_only_idle:
    assert property ( $rose(start_bit_detected) |-> $past(state)==IDLE && $past(Rx)==1'b0 );
  a_startflag_fall_only_parity:
    assert property ( $fell(start_bit_detected) |-> $past(state)==PARITY_BIT );

  // Only START_BIT writes data_bits
  a_data_written_only_in_start:
    assert property ( $changed(data_bits) |-> $past(state)==START_BIT );

  // Initialization coverage (observed on first clock)
  c_init: cover property ( $past($initstate) |-> state==IDLE && Tx==1 && data_bits==9'd0
                                        && parity_bit==0 && start_bit_detected==0 && bit_count==0 );

  // Functional coverage
  // A full frame: IDLE detect -> START -> some DATA_BITS -> PARITY -> IDLE
  c_full_frame: cover property (
      state==IDLE && Rx==0
      ##1 state==START_BIT
      ##1 (state==DATA_BITS)[*1:$]
      ##1 state==PARITY_BIT
      ##1 state==IDLE
  );
  // Parity output both values
  c_parity_tx0: cover property ( state==PARITY_BIT && Tx==1'b0 );
  c_parity_tx1: cover property ( state==PARITY_BIT && Tx==1'b1 );
  // Back-to-back frames
  c_back_to_back: cover property (
      state==PARITY_BIT ##1 state==IDLE && Rx==0 ##1 state==START_BIT
  );
endmodule

bind ps2 ps2_sva ps2_sva_i (.*);