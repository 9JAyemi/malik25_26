// SVA for axi_ad9152_if
// Bind into DUT; no TB code.

bind axi_ad9152_if axi_ad9152_if_sva();

module axi_ad9152_if_sva;

  // Clock mirroring: dac_clk must exactly follow tx_clk on both edges
  property p_clk_mirror;
    @(posedge tx_clk or negedge tx_clk) dac_clk == tx_clk;
  endproperty
  assert property (p_clk_mirror)
    else $error("dac_clk != tx_clk");

  // Reset behavior: when dac_rst is 1 on a rising edge, tx_data is 0 by the next edge
  property p_reset_clears;
    @(posedge dac_clk) dac_rst |-> ##1 (tx_data == 128'd0);
  endproperty
  assert property (p_reset_clears)
    else $error("tx_data not zero after reset");

  // No X/Z on tx_data (sampled on clock)
  assert property (@(posedge dac_clk) !$isunknown(tx_data))
    else $error("tx_data has X/Z");

  // Expected packing function (matches RTL byte ordering)
  function automatic [127:0] pack_expected(
    input [15:0] d00, d01, d02, d03,  // dac_data_0_*
    input [15:0] d10, d11, d12, d13   // dac_data_1_*
  );
    pack_expected = {
      d13[7:0], d12[7:0], d11[7:0], d10[7:0],
      d13[15:8], d12[15:8], d11[15:8], d10[15:8],
      d03[7:0], d02[7:0], d01[7:0], d00[7:0],
      d03[15:8], d02[15:8], d01[15:8], d00[15:8]
    };
  endfunction

  // Mapping check: when not in reset, next-cycle tx_data equals packed current inputs
  property p_pack_mapping;
    @(posedge dac_clk)
      !dac_rst |-> ##1
        tx_data == pack_expected($past(dac_data_0_0), $past(dac_data_0_1),
                                 $past(dac_data_0_2), $past(dac_data_0_3),
                                 $past(dac_data_1_0), $past(dac_data_1_1),
                                 $past(dac_data_1_2), $past(dac_data_1_3));
  endproperty
  assert property (p_pack_mapping)
    else $error("tx_data packing mismatch");

  // Stability: if all inputs are stable and no reset, tx_data holds next cycle
  property p_stability;
    @(posedge dac_clk)
      (!dac_rst && $stable({dac_data_0_0,dac_data_0_1,dac_data_0_2,dac_data_0_3,
                            dac_data_1_0,dac_data_1_1,dac_data_1_2,dac_data_1_3}))
      |-> ##1 (tx_data == $past(tx_data));
  endproperty
  assert property (p_stability)
    else $error("tx_data changed while inputs stable");

  // Minimal but meaningful coverage

  // Saw reset asserted
  cover property (@(posedge dac_clk) $rose(dac_rst));

  // Saw a non-zero packed output in normal operation
  cover property (@(posedge dac_clk) !dac_rst ##1 (tx_data != 128'd0));

  // Cover representative byte-lane propagation from both channels (low and high bytes)
  cover property (@(posedge dac_clk) !dac_rst |-> ##1
    (tx_data[127:120] == $past(dac_data_1_3[7:0])  &&
     tx_data[95:88]   == $past(dac_data_1_3[15:8]) &&
     tx_data[39:32]   == $past(dac_data_0_0[7:0])  &&
     tx_data[7:0]     == $past(dac_data_0_0[15:8])));

endmodule