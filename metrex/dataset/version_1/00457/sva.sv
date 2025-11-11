// SVA for can_transmitter
// Bind this module to can_transmitter to check and cover key behavior.

module can_transmitter_sva;
  // These names resolve inside the bound can_transmitter instance
  // clk, rst, inputs, outputs, and internal regs
  default clocking cb @(posedge clk); endclocking

  // Convenience constant
  localparam int K_LOAD = TQ * (BRP + 1) * (PROP + PHASE1 + PHASE2);

  // Basic sanity
  a_state_legal:        assert property (disable iff (rst) (state inside {4'h0,4'h1,4'h2,4'h3,4'h4,4'h5}));
  a_outputs_no_x:       assert property (!$isunknown({tx_en, tx_id, tx_dlc, tx_data, state}));

  // Reset behavior
  a_reset_vals:         assert property (rst |-> state==4'h0 && bit_counter==0 && tx_data==8'h00 && tx_id==11'h000 && tx_dlc==4'h0 && !tx_en);

  // Outputs mirror internal regs
  a_outs_equal_regs:    assert property (tx_en==tx_en_reg && tx_id==tx_id_reg && tx_dlc==tx_dlc_reg && tx_data==tx_data_reg);

  // Idle hold when no frame requested
  a_idle_hold:          assert property (disable iff (rst) (state==4'h0 && id==11'h000) |=> state==4'h0 && !tx_en);

  // Start of frame: capture inputs, enter state1, assert tx_en, load bit_counter
  a_start_capture:      assert property (disable iff (rst)
                             ($past(state)==4'h0 && state==4'h1) |-> ($past(id)!=11'h000 &&
                               tx_id==$past(id) && tx_dlc==$past(dlc) && tx_data==$past(data) && tx_en));

  a_load_counter:       assert property (disable iff (rst)
                             ($past(state)==4'h0 && state==4'h1) |-> (bit_counter==K_LOAD && bit_counter>0));

  // tx_en protocol
  a_tx_en_high_active:  assert property (disable iff (rst) (state inside {4'h1,4'h2,4'h3,4'h4,4'h5}) |-> tx_en);
  a_tx_en_low_idle:     assert property (disable iff (rst) (state==4'h0) |-> !tx_en);

  // Payload fields remain stable while transmitting (states 2..5)
  a_fields_stable_tx:   assert property (disable iff (rst) (state inside {4'h2,4'h3,4'h4,4'h5}) |-> $stable({tx_id,tx_dlc,tx_data}));

  // Ensure the captured ID/data/dlc equal the request that started the frame (catch unintended mutation in state1)
  a_fields_equal_req:   assert property (disable iff (rst)
                             ($past(state)==4'h1 && state==4'h2) |-> (tx_id==$past(id) && tx_dlc==$past(dlc) && tx_data==$past(data)));

  // Bit counter behavior in data/CRC/ACK/EOF states
  a_bc_decrement:       assert property (disable iff (rst)
                             (state inside {4'h2,4'h3,4'h4,4'h5} && bit_counter>0) |=> (state==$past(state) && bit_counter==$past(bit_counter)-1));

  a_bc_no_underflow:    assert property (disable iff (rst)
                             ($past(state inside {4'h2,4'h3,4'h4,4'h5}) && $past(bit_counter)==0) |-> bit_counter==0);

  // State advancement on bit_counter==0
  a_adv_2_to_3:         assert property (disable iff (rst) (state==4'h2 && bit_counter==0) |=> state==4'h3);
  a_adv_3_to_4:         assert property (disable iff (rst) (state==4'h3 && bit_counter==0) |=> state==4'h4);
  a_adv_4_to_5:         assert property (disable iff (rst) (state==4'h4 && bit_counter==0) |=> state==4'h5);
  a_adv_5_to_0:         assert property (disable iff (rst) (state==4'h5 && bit_counter==0) |=> (state==4'h0 && !tx_en));

  // Coverage: one complete successful frame through all phases
  c_full_frame:         cover property (disable iff (rst)
                             state==4'h0 && id!=11'h000
                             ##1 state==4'h1 && tx_en && bit_counter==K_LOAD
                             ##1 state==4'h2 [*1:$] ##1 state==4'h3 [*1:$]
                             ##1 state==4'h4 [*1:$] ##1 state==4'h5 [*1:$]
                             ##1 state==4'h0 && !tx_en);

  // Coverage: counter decrements to zero in any active state
  c_counter_runs_down:  cover property (disable iff (rst)
                             (state inside {4'h2,4'h3,4'h4,4'h5} && bit_counter==K_LOAD) ##[1:$] (bit_counter==0));

endmodule

// Bind into the DUT
bind can_transmitter can_transmitter_sva sva_inst();