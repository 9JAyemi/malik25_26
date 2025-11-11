// SVA for jt12_sh: bindable checker with concise, high-quality properties
module jt12_sh_sva #(parameter width=5, stages=24)
(
  input                  clk,
  input                  clk_en,
  input  [width-1:0]     din,
  input  [width-1:0]     drop
);

  default clocking cb @(posedge clk); endclocking

  // Shift-event spacer: advance to the next cycle with clk_en==1, allowing any number of disabled cycles
  sequence next_en; (!clk_en)[*0:$] ##1 clk_en; endsequence

  // Sanity: clk_en should never be X/Z
  assert property (!$isunknown(clk_en));

  // When not enabled, output must hold its value
  assert property (!clk_en |-> $stable(drop));

  // If drop changes, it must be on an enabled cycle
  assert property ($changed(drop) |-> clk_en);

  genvar i;
  generate
    for (i = 0; i < width; i++) begin : per_bit

      // Core functional spec: drop[i] equals din[i] delayed by exactly 'stages' enable events (with gaps allowed).
      // Use ##0 to check post-NBA update at the last enable event.
      property p_delay_by_en_events;
        bit s;
        (clk_en && !$isunknown(din[i]), s = din[i])
        ##1 next_en[* (stages-1)]
        ##0 (drop[i] == s);
      endproperty
      assert property (p_delay_by_en_events);

      // Simplified check for the special case of consecutive enables: after 'stages' consecutive enables,
      // drop matches din from exactly 'stages' cycles ago.
      assert property ( clk_en[*stages] ##0 (drop[i] == $past(din[i], stages)) );

      // Coverage: demonstrate both 0 and 1 values propagate through the shifter for each bit
      property p_cover_val0;
        (clk_en && (din[i] == 1'b0))
        ##1 next_en[* (stages-1)]
        ##0 (drop[i] == 1'b0);
      endproperty
      cover property (p_cover_val0);

      property p_cover_val1;
        (clk_en && (din[i] == 1'b1))
        ##1 next_en[* (stages-1)]
        ##0 (drop[i] == 1'b1);
      endproperty
      cover property (p_cover_val1);

      // Coverage: at least one disabled gap occurs between enable events while value propagates (only meaningful for stages>=2)
      if (stages >= 2) begin : gap_cov
        cover property (
          (clk_en)
          ##1 (!clk_en[*1:$] ##1 clk_en)                 // ensure there is a real gap before the next enable
          ##1 next_en[* (stages-2)]
          ##0 (drop[i] == $past(din[i], $past_gclk(1)+1)) // end-to-end observe new value; exact past depth not critical for cover
        );
      end
    end
  endgenerate
endmodule

// Bind into the DUT
bind jt12_sh jt12_sh_sva #(.width(width), .stages(stages))
  jt12_sh_sva_i (.clk(clk), .clk_en(clk_en), .din(din), .drop(drop));