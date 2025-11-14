// SVA for spi_core. Bind this file; focuses on key protocol/functional checks and compact coverage.

module spi_core_sva #(parameter int BITS_IN_BYTE=8,
                      parameter int NBIT_BIT_CTR=3,
                      parameter int NBIT_BYTE_CTR=3) ();

  // Basic combinational relationships
  assert property (@(posedge sck_core or negedge sck_core)
                   o_spi_active == (i_rstb && (i_epol ^ i_cs)));
  assert property (@(posedge sck_core or negedge sck_core)
                   o_drvb == !o_spi_active);
  assert property (@(posedge i_sck or negedge i_sck or posedge sck_core or negedge sck_core)
                   sck_core == (i_cpha ^ i_cpol ^ i_sck));
  assert property (@(posedge sck_core or negedge sck_core)
                   vo_data_rx == {rv_rx, i_sdi});
  assert property (@(posedge sck_core or negedge sck_core)
                   o_sdo == rv_tx[rv_tx_ptr]);
  assert property (@(posedge sck_core or negedge sck_core)
                   rv_tx_ptr <= BITS_IN_BYTE-1);

  // Idle/reset invariants while not selected
  assert property (@(posedge sck_core)
                   !chip_select |-> (rv_tx_ptr == BITS_IN_BYTE-1
                                   && vo_byte_num == '0
                                   && rv_tx == '0
                                   && rv_rx == '0
                                   && o_rx_valid == 1'b0
                                   && o_drvb == 1'b1
                                   && o_spi_active == 1'b0));

  // TX bit pointer progression (every negedge sck_core while selected)
  assert property (@(negedge sck_core)
                   chip_select && $past(chip_select)
                   |-> ( ($past(rv_tx_ptr) == '0)
                         ? (rv_tx_ptr == BITS_IN_BYTE-1)
                         : (rv_tx_ptr == $past(rv_tx_ptr) - 1) ));

  // Byte counter updates only at byte boundary
  assert property (@(negedge sck_core)
                   chip_select && $past(chip_select)
                   |-> ( vo_byte_num ==
                         ( ($past(rv_tx_ptr) == '0)
                           ? ($past(vo_byte_num) + 1)
                           : $past(vo_byte_num) ) ));

  // TX data stable between loads
  assert property (@(negedge sck_core)
                   chip_select && $past(chip_select) && ($past(rv_tx_ptr) != '0)
                   |-> (rv_tx == $past(rv_tx)));

  // RX valid = end-of-byte, single-cycle pulse at posedge
  assert property (@(posedge sck_core)
                   chip_select |-> (o_rx_valid == (rv_tx_ptr == '0)));
  assert property (@(posedge sck_core)
                   $rose(o_rx_valid) |=> !o_rx_valid);

  // No RX shifting on end-of-byte posedge
  assert property (@(posedge sck_core)
                   chip_select && (rv_tx_ptr == '0) |-> $stable(rv_rx));

  // No X on primaries when idle
  assert property (@(posedge sck_core)
                   !chip_select |-> !$isunknown({o_sdo,o_drvb,o_spi_active,o_rx_valid,vo_byte_num,vo_data_rx}));

  // Compact functional coverage
  // Byte reload event (ptr 0 -> reload)
  cover property (@(negedge sck_core)
                  chip_select && $past(chip_select) && ($past(rv_tx_ptr) == '0) && (rv_tx_ptr == BITS_IN_BYTE-1));
  // RX valid pulse observed
  cover property (@(posedge sck_core) chip_select && $rose(o_rx_valid));
  // Exercise both CPOL/CPHA parity modes
  cover property (@(posedge i_sck) (i_cpol ^ i_cpha) == 1'b0);
  cover property (@(posedge i_sck) (i_cpol ^ i_cpha) == 1'b1);
  // CS activity
  cover property (@(posedge i_sck or negedge i_sck) $rose(chip_select));
  cover property (@(posedge i_sck or negedge i_sck) $fell(chip_select));

endmodule

bind spi_core spi_core_sva #(.BITS_IN_BYTE(BITS_IN_BYTE),
                             .NBIT_BIT_CTR(NBIT_BIT_CTR),
                             .NBIT_BYTE_CTR(NBIT_BYTE_CTR)) u_spi_core_sva();