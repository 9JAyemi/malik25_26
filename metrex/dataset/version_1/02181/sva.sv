// Bind these SVA to the DUT
bind lin_transmitter lin_transmitter_sva();

module lin_transmitter_sva();

  // Access DUT scope signals/params directly
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Local copies of state encodings for readability
  localparam logic [1:0] S_IDLE = 2'b00;
  localparam logic [1:0] S_SYNC = 2'b01;
  localparam logic [1:0] S_ID   = 2'b10;
  localparam logic [1:0] S_DATA = 2'b11;

  // Reset behavior
  assert property (rst |=> state==S_IDLE && bit_count==0 && checksum==8'd0 && tx==1);

  // Bitcount always in range
  assert property (1'b1 |-> (bit_count inside {[0:7]}));

  // Idle behavior
  assert property (state==S_IDLE && !tx_en |=> state==S_IDLE);
  assert property (state==S_IDLE |-> tx==1);

  // Start-of-frame kick: latch SYNC field and enter SYNC
  assert property (state==S_IDLE && tx_en |=> state==S_SYNC && frame[7:0]==8'h55);

  // Mid-step pattern (counts 0..6): increment bit_count and drive alternating tx
  property p_step_mid (logic [1:0] s);
    (state==s && (bit_count inside {[0:6]}))
    |=> (state==s &&
         bit_count == $past(bit_count)+1 &&
         tx == (($past(bit_count)%2)==0 ? 1'b0 : 1'b1));
  endproperty
  assert property (p_step_mid(S_SYNC));
  assert property (p_step_mid(S_ID));
  assert property (p_step_mid(S_DATA));

  // Last step (count==7): tx=1, wrap bit_count to 0, advance state
  property p_step_last (logic [1:0] s, logic [1:0] n);
    (state==s && bit_count==7) |=> (tx==1 && bit_count==0 && state==n);
  endproperty
  assert property (p_step_last(S_SYNC, S_ID));
  assert property (p_step_last(S_ID,   S_DATA));
  assert property (p_step_last(S_DATA, S_IDLE));

  // Allowed transitions only
  assert property ((state==S_IDLE) |=> (state==S_IDLE || state==S_SYNC));
  assert property ((state==S_SYNC) |=> (state==S_SYNC || state==S_ID));
  assert property ((state==S_ID)   |=> (state==S_ID   || state==S_DATA));
  assert property ((state==S_DATA) |=> (state==S_DATA || state==S_IDLE));

  // Checksum behavior
  // Load with ID at end of SYNC
  assert property ((state==S_SYNC && bit_count==7) |=> checksum == id);
  // Accumulate data at end of ID
  assert property ((state==S_ID && bit_count==7) |=> checksum == $past(checksum) + tx_data);
  // Stable elsewhere
  assert property ((state==S_SYNC && bit_count inside {[0:6]}) |=> $stable(checksum));
  assert property ((state==S_ID   && bit_count inside {[0:6]}) |=> $stable(checksum));
  assert property ((state==S_DATA && bit_count inside {[0:7]}) |=> $stable(checksum));

  // Frame field writes (check essential bits)
  // ID slice on SYNC->ID boundary (check 1+6 LSBs of slice)
  assert property ((state==S_SYNC && bit_count==7)
                   |=> frame[SYNC_BYTE+6 : SYNC_BYTE] == {1'b0, id});
  // DATA slice on ID->DATA boundary
  assert property ((state==S_ID && bit_count==7)
                   |=> frame[DATA_BYTE+ID_BYTE+SYNC_BYTE-1 : ID_BYTE+SYNC_BYTE] == tx_data);
  // CHECKSUM slice on DATA->IDLE boundary (check low 8 bits)
  assert property ((state==S_DATA && bit_count==7)
                   |=> frame[DATA_BYTE+ID_BYTE+SYNC_BYTE+7 : DATA_BYTE+ID_BYTE+SYNC_BYTE]
                       == ~ $past(checksum));

  // End-to-end coverage: one complete frame
  cover property (
    state==S_IDLE && tx_en
    ##1 state==S_SYNC && bit_count==1
    ##[6] state==S_ID   && bit_count==1
    ##[6] state==S_DATA && bit_count==1
    ##1 state==S_IDLE);

  // Boundary transition coverage
  cover property (state==S_SYNC && bit_count==7 ##1 state==S_ID);
  cover property (state==S_ID   && bit_count==7 ##1 state==S_DATA);
  cover property (state==S_DATA && bit_count==7 ##1 state==S_IDLE);

endmodule