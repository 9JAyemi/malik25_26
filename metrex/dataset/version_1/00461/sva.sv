// SVA for AR_TXD
// Bind these assertions to the DUT
bind AR_TXD AR_TXD_SVA u_AR_TXD_SVA();

module AR_TXD_SVA (AR_TXD dut);

  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (dut.reset);

  // Basic combinational relationships
  assert property (dut.start == (dut.st && !dut.en_tx_word));
  assert property (dut.SLP   == (dut.Nvel == 2'b00));
  assert property (dut.T_cp  == (dut.cb_bit == 6'd31));
  assert property (dut.ce_tact == (dut.cb_tce == dut.AR_Nt));
  assert property (dut.ce    == (dut.ce_tact && dut.QM));
  assert property (dut.ce_end_word == ((dut.cb_bit == 6'd35) && dut.ce));
  assert property (dut.T_adr_dat == (dut.en_tx && !dut.T_cp));
  assert property (dut.SDAT  == (dut.sr_adr[7] | (dut.T_cp && dut.FT_cp)));

  // TXD correctness and exclusivity
  assert property (!(dut.TXD1 && dut.TXD0));
  assert property ((dut.en_tx && dut.QM) == (dut.TXD1 ^ dut.TXD0));
  assert property (dut.TXD1 |-> (dut.en_tx && dut.QM && dut.SDAT));
  assert property (dut.TXD0 |-> (dut.en_tx && dut.QM && !dut.SDAT));

  // Ranges / safety
  assert property (dut.cb_bit <= 6'd35);

  // cb_tce/ce_tact timing
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   (dut.start || dut.ce_tact) |=> (dut.cb_tce == 11'd1));
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   !(dut.start || dut.ce_tact) |=> (dut.cb_tce == $past(dut.cb_tce)+11'd1));

  // QM behavior
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   dut.start |=> (dut.QM == 1'b0));
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   (dut.en_tx && dut.ce_tact && !dut.start) |=> (dut.QM == !$past(dut.QM)));
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   !(dut.en_tx && dut.ce_tact) && !dut.start |=> (dut.QM == $past(dut.QM)));

  // cb_bit progression
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   dut.start |=> (dut.cb_bit == 6'd0));
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   (dut.en_tx_word && dut.ce && !dut.start) |=> (dut.cb_bit == $past(dut.cb_bit)+6'd1));
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   !(dut.en_tx_word && dut.ce) && !dut.start |=> (dut.cb_bit == $past(dut.cb_bit)));

  // en_tx_word update
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   dut.start |=> dut.en_tx_word);
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   dut.ce_end_word |=> !dut.en_tx_word);
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   !dut.start && !dut.ce_end_word |=> (dut.en_tx_word == $past(dut.en_tx_word)));

  // en_tx update
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   dut.start |=> dut.en_tx);
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   (dut.T_cp && dut.ce) |=> !dut.en_tx);
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   !dut.start && !(dut.T_cp && dut.ce) |=> (dut.en_tx == $past(dut.en_tx)));

  // FT_cp update
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   (dut.start || (dut.T_cp && dut.ce)) |=> dut.FT_cp);
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   (dut.sr_adr[7] && dut.ce && dut.T_adr_dat) |=> (dut.FT_cp == !$past(dut.FT_cp)));
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   !(dut.start || (dut.T_cp && dut.ce) || (dut.sr_adr[7] && dut.ce && dut.T_adr_dat))
                   |=> (dut.FT_cp == $past(dut.FT_cp)));

  // Shift register behavior
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   dut.start |=> (dut.sr_adr == dut.ADR));
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   dut.start |=> (dut.sr_dat == dut.DAT));
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   (dut.ce && dut.en_tx && !dut.start)
                   |=> (dut.sr_adr == { $past(dut.sr_adr[6:0]), $past(dut.sr_dat[0]) }));
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   (dut.ce && dut.en_tx && !dut.start)
                   |=> (dut.sr_dat == { 1'b0, $past(dut.sr_dat[22:1]) }));
  assert property (disable iff (dut.reset || (dut.cb_bit==6'd32))
                   !(dut.ce && dut.en_tx) && !dut.start
                   |=> (dut.sr_adr == $past(dut.sr_adr) && dut.sr_dat == $past(dut.sr_dat)));

  // Coverage (functional)
  cover property (dut.start);
  cover property (dut.ce_tact);
  cover property (dut.T_cp && dut.ce);
  cover property (dut.ce_end_word); // if never covered, flags potential end-of-word issue
  cover property (dut.sr_adr[7] && dut.ce && dut.T_adr_dat);
  cover property (dut.TXD0);
  cover property (dut.TXD1);
  cover property (dut.Nvel == 2'b00);
  cover property (dut.Nvel == 2'b01);
  cover property (dut.Nvel == 2'b10);
  cover property (dut.Nvel == 2'b11);

endmodule