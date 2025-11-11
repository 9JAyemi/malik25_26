// SystemVerilog Assertions for parallel_port
// Bind into the DUT so we can see internal regs
bind parallel_port parallel_port_sva();

module parallel_port_sva;

  // Use the DUT clock; disable most checks during reset
  default clocking cb @(posedge clk_i); endclocking
  default disable iff (rst_i);

  // Basic structural/pass-through checks
  ap_parport_passthru: assert property (parport_o === parport_i);

  // Combinational read datapath mux
  ap_datao_mux: assert property (
    data_o === ((address_i==2'b00) ? parport_i[7:0] :
                (address_i==2'b01) ? inputreg_r[7:0] :
                (address_i==2'b10) ? inputreg_r[15:8] :
                                     inputreg_r[23:16])
  );

  // Combinational read strobe mapping
  ap_readstrobe_map: assert property (
    parport_readstrobe_o === (readstrobe_i && (address_i==2'b00))
  );

  // outputreg_r reset behavior (checked even when reset asserted)
  ap_outreg_reset_set:  assert property (@(posedge clk_i) rst_i |=> (outputreg_r==24'h0));
  ap_outreg_reset_hold: assert property (@(posedge clk_i) (rst_i && $past(rst_i)) |-> (outputreg_r==24'h0));

  // Writes to output register update only targeted byte-lane
  ap_wr00_updates: assert property (
    writestrobe_i && address_i==2'b00 |=> (outputreg_r[7:0]   == $past(data_i) &&
                                           outputreg_r[23:8]  == $past(outputreg_r[23:8]))
  );
  ap_wr01_updates: assert property (
    writestrobe_i && address_i==2'b01 |=> (outputreg_r[15:8]  == $past(data_i) &&
                                           outputreg_r[23:16] == $past(outputreg_r[23:16]) &&
                                           outputreg_r[7:0]   == $past(outputreg_r[7:0]))
  );
  ap_wr10_updates: assert property (
    writestrobe_i && address_i==2'b10 |=> (outputreg_r[23:16] == $past(data_i) &&
                                           outputreg_r[15:0]  == $past(outputreg_r[15:0]))
  );
  ap_wr11_no_outreg_write: assert property (
    writestrobe_i && address_i==2'b11 |=> $stable(outputreg_r)
  );

  // No write => outputreg_r holds value (reads do not modify it)
  ap_outreg_holds_no_write: assert property (
    !writestrobe_i |=> $stable(outputreg_r)
  );

  // inputreg_r capture only on read of address 00 when not writing
  ap_inreg_capture: assert property (
    (readstrobe_i && address_i==2'b00 && !writestrobe_i) |=> (inputreg_r == $past(parport_i[31:8]))
  );
  ap_inreg_stable_otherwise: assert property (
    !(readstrobe_i && address_i==2'b00 && !writestrobe_i) |=> $stable(inputreg_r)
  );

  // parport_writestrobe_o: one-cycle pulse only on write to addr 11
  ap_pwso_assert_on_write11: assert property (
    (writestrobe_i && address_i==2'b11) |-> ##0 parport_writestrobe_o
  );
  ap_pwso_deassert_next: assert property (
    parport_writestrobe_o |-> ##1 !parport_writestrobe_o
  );
  ap_pwso_has_cause: assert property (
    parport_writestrobe_o |-> $past(writestrobe_i && address_i==2'b11)
  );
  ap_pwso_no_false_addr: assert property (
    (writestrobe_i && address_i!=2'b11) |-> ##0 !parport_writestrobe_o
  );

  // Functional coverage
  cp_write_00: cover property (writestrobe_i && address_i==2'b00);
  cp_write_01: cover property (writestrobe_i && address_i==2'b01);
  cp_write_10: cover property (writestrobe_i && address_i==2'b10);
  cp_write_11: cover property (writestrobe_i && address_i==2'b11 && ##0 parport_writestrobe_o);

  cp_read_cap_00: cover property (readstrobe_i && address_i==2'b00 && !writestrobe_i && ##1 $stable(inputreg_r));
  cp_read_after_cap_01: cover property ((readstrobe_i && address_i==2'b00 && !writestrobe_i) ##1 (address_i==2'b01));
  cp_read_after_cap_10: cover property ((readstrobe_i && address_i==2'b00 && !writestrobe_i) ##1 (address_i==2'b10));
  cp_read_after_cap_11: cover property ((readstrobe_i && address_i==2'b00 && !writestrobe_i) ##1 (address_i==2'b11));

  cp_parport_readstrobe_o: cover property (parport_readstrobe_o);
  cp_parport_writestrobe_o: cover property (parport_writestrobe_o);

endmodule