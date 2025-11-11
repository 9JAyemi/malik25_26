// SVA for binary_to_bcd
// Bind into the DUT scope so we can directly reference internals like temp.

bind binary_to_bcd binary_to_bcd_sva u_binary_to_bcd_sva();

module binary_to_bcd_sva;

  default clocking cb @(posedge clk); endclocking

  // Reset/Clear behavior (synchronous)
  a_reset_next_zero: assert property (
    reset |=> (temp==24'd0 && out1==4'd0 && out2==4'd0 && out3==4'd0 && out4==4'd0)
  );
  a_clear_next_zero: assert property (
    (!reset && clear) |=> (temp==24'd0 && out1==4'd0 && out2==4'd0 && out3==4'd0 && out4==4'd0)
  );

  // Next-state function of temp (captures multiple non-blocking assignments semantics)
  // If prior temp >= 10,000 then next temp = prior temp + 3
  a_temp_add3: assert property (
    (!reset && !clear && temp >= 24'd10000) |=> (temp == $past(temp) + 24'd3)
  );
  // Else, next temp = {prior temp[15:0], prior in} (note truncation of {temp[19:0],in})
  a_temp_shift: assert property (
    (!reset && !clear && temp < 24'd10000) |=> (temp == { $past(temp[15:0]), $past(in) })
  );

  // Outputs mirror prior temp nibbles
  a_out_map: assert property (
    (!reset && !clear) |=> ({out4,out3,out2,out1} ==
                            $past({temp[15:12],temp[11:8],temp[7:4],temp[3:0]}))
  );

  // No X/Z on state/outputs after reset is deasserted
  a_no_x: assert property (@(posedge clk) disable iff (reset)
    !$isunknown({out1,out2,out3,out4,temp})
  );

  // Coverage
  c_reset:          cover property (reset ##1 (temp==0 && out1==0 && out2==0 && out3==0 && out4==0));
  c_clear:          cover property (!reset && clear ##1 (temp==0 && out1==0 && out2==0 && out3==0 && out4==0));
  c_shift_branch:   cover property (!reset && !clear && temp < 24'd10000 ##1 (temp == { $past(temp[15:0]), $past(in) }));
  c_add3_branch:    cover property (!reset && !clear && temp >= 24'd10000 ##1 (temp == $past(temp)+24'd3));
  c_high_threshold: cover property (!reset && !clear && temp >= 24'd10000000);

endmodule