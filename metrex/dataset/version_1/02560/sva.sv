// SVA for delay_calc
// Bind this module to the DUT: bind delay_calc delay_calc_sva sv(.dut(<instance_name>));

module delay_calc_sva (delay_calc dut);
  default clocking cb @(posedge dut.clk40); endclocking

  // Local helpers
  function automatic logic [5:0] sat6_from8 (input logic [7:0] v);
    return (v[7]) ? 6'd0 : ((v[6:0] > 7'd63) ? 6'd63 : v[5:0]);
  endfunction
  function automatic logic sat_flag_from8 (input logic [7:0] v);
    return v[7] || (v[6:0] > 7'd63);
  endfunction

  let data_sum = 8'd32
                 + {dut.data_offset_delay[6], dut.data_offset_delay}
                 + {dut.delay_modifier[6],   dut.delay_modifier}
                 + (8'b1 + ~dut.scan_delay);
  let drdy_sum = 8'd32
                 + {dut.delay_modifier[6], dut.delay_modifier}
                 + (8'b1 + ~dut.scan_delay);

  // Reset behavior (registered at next cycle)
  assert property ($past(dut.rst) |-> dut.adc_clock_delay == 6'd0
                               &&  dut.adc_data_delay_2s == 8'd0
                               &&  dut.adc_drdy_delay_2s == 8'd0)
    else $error("Reset did not clear registers");

  // Register updates when strb is high
  assert property (disable iff (dut.rst)
                   dut.strb |=> dut.adc_clock_delay   == $past(dut.scan_delay))
    else $error("adc_clock_delay update mismatch");
  assert property (disable iff (dut.rst)
                   dut.strb |=> dut.adc_data_delay_2s == $past(data_sum))
    else $error("adc_data_delay_2s update mismatch");
  assert property (disable iff (dut.rst)
                   dut.strb |=> dut.adc_drdy_delay_2s == $past(drdy_sum))
    else $error("adc_drdy_delay_2s update mismatch");

  // Hold registers when strb is low (unless reset asserted)
  assert property ((!dut.rst && !dut.strb) |=> ($stable(dut.adc_clock_delay)
                                             && $stable(dut.adc_data_delay_2s)
                                             && $stable(dut.adc_drdy_delay_2s)) or dut.rst)
    else $error("Registers changed without strb");

  // Combinational mapping: saturation and outputs
  assert property (dut.adc_data_delay == sat6_from8(dut.adc_data_delay_2s))
    else $error("adc_data_delay mapping error");
  assert property (dut.adc_drdy_delay == sat6_from8(dut.adc_drdy_delay_2s))
    else $error("adc_drdy_delay mapping error");
  assert property (dut.saturated == (sat_flag_from8(dut.adc_data_delay_2s)
                                  || sat_flag_from8(dut.adc_drdy_delay_2s)))
    else $error("saturated flag mapping error");

  // Basic sanity: no X/Z on outputs when not in reset
  assert property (!dut.rst |-> !$isunknown({dut.adc_clock_delay,
                                            dut.adc_data_delay,
                                            dut.adc_drdy_delay,
                                            dut.saturated})))
    else $error("Output has X/Z");

  // Targeted coverage
  cover property (disable iff (dut.rst) dut.strb); // update event
  cover property (disable iff (dut.rst) dut.strb ##1 dut.adc_data_delay_2s[7]); // data negative clamp
  cover property (disable iff (dut.rst) dut.strb ##1 dut.adc_drdy_delay_2s[7]); // drdy negative clamp
  cover property (disable iff (dut.rst) dut.strb ##1 (!dut.adc_data_delay_2s[7] && (dut.adc_data_delay_2s[6:0] > 7'd63))); // data high clamp
  cover property (disable iff (dut.rst) dut.strb ##1 (!dut.adc_drdy_delay_2s[7] && (dut.adc_drdy_delay_2s[6:0] > 7'd63))); // drdy high clamp
  cover property (disable iff (dut.rst) dut.strb ##1 (!sat_flag_from8(dut.adc_data_delay_2s)
                                                   && !sat_flag_from8(dut.adc_drdy_delay_2s))); // no saturation
  cover property (!dut.rst && !dut.strb ##1 $stable({dut.adc_clock_delay,
                                                     dut.adc_data_delay_2s,
                                                     dut.adc_drdy_delay_2s})); // hold path

endmodule