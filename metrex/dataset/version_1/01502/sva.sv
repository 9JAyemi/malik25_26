// SVA checker for my_RAM64X1D2
module my_RAM64X1D2_sva;
  default clocking cb @(posedge clk); endclocking

  // Combinational decode from din (note: addr2 effectively truncates to {din[4:0],1'b0})
  ap_decode_map: assert property (
    !$isunknown(din) |-> (addr1 == din[5:0] && addr2 == {din[4:0],1'b0} && read_en == din[6:5] && write_en == din[7])
  );

  // dout changes only on a read
  ap_dout_no_spurious_change: assert property ( (read_en == 2'b00) |=> $stable(dout) );
  ap_dout_change_implies_read: assert property ( $changed(dout) |-> $past(read_en != 2'b00) );

  // Read behavior: dout reflects prior-cycle RAM[addr2]
  ap_read_effect: assert property (
    (!$isunknown({read_en,addr2})) && (read_en != 2'b00) |=> (dout == $past(ram[$past(addr2)]))
  );

  // Write behavior: RAM[addr1] updates with din; no write when write_en=0
  ap_write_effect: assert property (
    (!$isunknown({write_en,addr1,din}) && write_en) |=> (ram[$past(addr1)] == $past(din))
  );
  ap_no_write_when_we0: assert property (
    !write_en |=> (ram[$past(addr1)] == $past(ram[$past(addr1)]))
  );

  // Simultaneous read & write same address: read gets old data, RAM gets new data
  ap_raw_same_addr: assert property (
    (write_en && (read_en != 2'b00) && (addr1 == addr2) && !$isunknown({addr1,addr2,din})) |=> 
      (dout == $past(ram[$past(addr2)]) && ram[$past(addr1)] == $past(din))
  );

  // Functional coverage
  cp_write_only:  cover property ( write_en && (read_en == 2'b00) );
  cp_read0_only:  cover property ( read_en == 2'b01 );
  cp_read1_only:  cover property ( read_en == 2'b10 );
  cp_read_both:   cover property ( read_en == 2'b11 );
  cp_wr_and_rd:   cover property ( write_en && (read_en != 2'b00) );
  cp_raw_same:    cover property ( write_en && (read_en != 2'b00) && (addr1 == addr2) );
  cp_b2b_wr:      cover property ( write_en ##1 write_en );
  cp_b2b_rd:      cover property ( (read_en != 2'b00) ##1 (read_en != 2'b00) );
endmodule

bind my_RAM64X1D2 my_RAM64X1D2_sva sva_inst();