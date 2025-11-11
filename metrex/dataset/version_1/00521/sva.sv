// SVA for softusb_tx
// Bind into the DUT to access internals
bind softusb_tx softusb_tx_sva();

module softusb_tx_sva;

  default clocking cb @(posedge usb_clk); endclocking
  default disable iff (usb_rst);

  // Reset/state update basics
  assert property (@(posedge usb_clk) usb_rst |=> state == IDLE);
  assert property (!gce |=> $stable(state));

  // GCE generation correctness
  assert property (gce |-> (gce_counter == 6'd0));
  assert property (gce |-> ($past(gce_counter) == (low_speed ? 6'd47 : 6'd5)));
  assert property (gce |=> !gce);

  // Output stage pipelines
  assert property (txp  == $past(txp_r));
  assert property (txm  == $past(txm_r));
  assert property (txoe == $past(txoe_r));

  // Internal outputs only change on gce (or reset)
  assert property (!gce |=> $stable({txp_r, txm_r, txoe_r}));

  // txoe_ctl per state
  assert property ( (state == IDLE) -> !txoe_ctl );
  assert property ( (state inside {DATA,EOP1,EOP2,J,GEOP1,GEOP2,GJ}) -> txoe_ctl );

  // generate_* per state and mutual exclusion
  assert property (!(generate_se0 && generate_j));
  assert property ( (state inside {EOP1,EOP2,GEOP1,GEOP2}) -> (generate_se0 && !generate_j) );
  assert property ( (state inside {J,GJ}) -> (generate_j && !generate_se0) );
  assert property ( (state inside {IDLE,DATA}) -> (!generate_se0 && !generate_j) );

  // tx_ready semantics
  assert property (tx_ready |-> (gce && tx_ready0));

  // txoe_r follows ctl on gce
  assert property (gce |-> (txoe_r == txoe_ctl));

  // Line driving behavior at each gce
  // Idle/J when not driving
  assert property (gce && !txoe_ctl |-> (txp_r == ~low_speed && txm_r == low_speed));
  // SE0
  assert property (gce && txoe_ctl && generate_se0 |-> (txp_r == 1'b0 && txm_r == 1'b0));
  // J
  assert property (gce && txoe_ctl && generate_j   |-> (txp_r == ~low_speed && txm_r == low_speed));
  // NRZI data: toggle on 0, hold on 1; non-SE0 implies complement
  assert property (gce && txoe_ctl && !generate_se0 && !generate_j && (sr_out == 1'b0)
                   |-> (txp_r == ~$past(txp_r) && txm_r == ~$past(txm_r)));
  assert property (gce && txoe_ctl && !generate_se0 && !generate_j && (sr_out == 1'b1)
                   |-> (txp_r ==  $past(txp_r) && txm_r ==  $past(txm_r)));
  assert property (gce && txoe_ctl && !generate_se0 |-> (txp_r == ~txm_r));

  // FSM transitions on gce
  // IDLE -> DATA handshake
  assert property (gce && state==IDLE && !generate_eop_pending && tx_valid
                   |-> (sr_load && tx_ready) ##1 (state==DATA));
  // IDLE -> GEOP1 on pending EOP
  assert property (gce && state==IDLE && generate_eop_pending |-> ##1 (state==GEOP1));
  // DATA autoload vs EOP
  assert property (gce && state==DATA && sr_done && transmission_continue
                   |-> (sr_load && tx_ready) ##1 (state==DATA));
  assert property (gce && state==DATA && sr_done && !transmission_continue
                   |-> ##1 (state==EOP1));
  // EOP sequencing
  assert property (gce && state==EOP1 |-> generate_se0 ##1 (state==EOP2));
  assert property (gce && state==EOP2 |-> generate_se0 ##1 (state==J));
  assert property (gce && state==J    |-> generate_j   ##1 (state==IDLE));
  // Generate-EOP sequencing and clear
  assert property (gce && state==GEOP1 |-> generate_se0 ##1 (state==GEOP2));
  assert property (gce && state==GEOP2 |-> generate_se0 ##1 (state==GJ));
  assert property (gce && state==GJ    |-> (generate_j && generate_eop_clear) ##1 (state==IDLE && !generate_eop_pending));

  // Shift register: reset and load effects
  assert property (sr_rst |-> (sr_done && onecount==3'd0 && sr_out==1'b1));
  assert property (gce && sr_load
                   |-> (!sr_done && bitcount==3'd0 && sr_out==tx_data[0] && sr==tx_data[7:1]
                        && (tx_data[0] ? (onecount==$past(onecount)+3'd1)
                                       : (onecount==3'd0))));

  // Shifting without stuffing (uses previous sr/onecount bits)
  assert property (gce && !sr_done && !sr_load && ($past(onecount) != 3'd6)
                   |-> (sr_out == $past(sr[0])
                        && bitcount == $past(bitcount)+3'd1
                        && sr == {1'b0, $past(sr[6:1])}
                        && ( $past(sr[0]) ? (onecount == $past(onecount)+3'd1)
                                          : (onecount == 3'd0))));

  // Bit-stuff insertion (6 ones -> stuff 0, hold sr/bitcount)
  assert property (gce && !sr_load && !sr_done && ($past(onecount)==3'd6)
                   |-> (sr_out==1'b0 && onecount==3'd0 && $stable(bitcount) && $stable(sr)));

  // Coverage
  cover property (gce && !low_speed);         // full-speed tick seen
  cover property (gce &&  low_speed);         // low-speed tick seen
  cover property (gce && state==IDLE && tx_valid && !generate_eop_pending ##1 state==DATA);
  cover property (gce && state==DATA && sr_done && !transmission_continue
                  ##1 state==EOP1 ##1 state==EOP2 ##1 state==J ##1 state==IDLE);
  cover property (gce && state==IDLE && generate_eop_pending
                  ##1 state==GEOP1 ##1 state==GEOP2 ##1 state==GJ ##1 state==IDLE);
  cover property (gce && txoe_ctl && !generate_se0 && !generate_j && (sr_out==0)); // NRZI toggle
  cover property (gce && !sr_done && ($past(onecount)==3'd6)); // bit-stuff event

endmodule