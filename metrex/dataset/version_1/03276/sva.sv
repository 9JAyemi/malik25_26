// SVA for seven_segment_controller
// Bindable assertion module (accesses internal 'digit')
module seven_segment_controller_sva(
  input logic        clk,
  input logic        reset,
  input logic        button,
  input logic [3:0]  digit,
  input logic [6:0]  leds
);

  // LED decode used by assertions
  function automatic logic [6:0] decode(input logic [3:0] d);
    case (d)
      4'd0: decode = 7'b0000001;
      4'd1: decode = 7'b1001111;
      4'd2: decode = 7'b0010010;
      4'd3: decode = 7'b0000110;
      4'd4: decode = 7'b1001100;
      4'd5: decode = 7'b0100100;
      4'd6: decode = 7'b0100000;
      4'd7: decode = 7'b0001111;
      4'd8: decode = 7'b0000000;
      4'd9: decode = 7'b0000100;
      default: decode = 7'b1111111;
    endcase
  endfunction

  // track past-valid to avoid $past at time 0
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset || !past_valid);

  // Async reset takes effect immediately
  assert property (@(posedge reset) ##0 (digit==4'd0 && leds==7'b0000001));
  // While reset is 1 at a clock, outputs reflect reset state
  assert property (@(posedge clk) reset |-> (digit==4'd0 && leds==7'b0000001));

  // Hold behavior when button=0
  assert property (!button |-> $stable(digit) && $stable(leds));

  // Increment behavior when button=1
  assert property (button |-> digit == ($past(digit)+4'd1));

  // LED decode uses previous digit value on button press
  assert property (button |-> leds == decode($past(digit)));

  // Registers only change due to button or reset
  assert property ($changed(digit) |-> $past(button));
  assert property ($changed(leds)  |-> $past(button));

  // No X/Z when not in reset
  assert property (!$isunknown({digit,leds}));

  // Coverage
  // Hit each decoded digit 0..9 on a press
  genvar i;
  generate
    for (i=0; i<10; i++) begin: cov_dec
      cover property (button && $past(digit)==i && leds == decode(i[3:0]));
    end
  endgenerate
  // Default decode used (digit>=10) on a press
  cover property (button && ($past(digit) >= 4'd10) && leds==7'b1111111);
  // Wrap-around from 4'hF -> 0
  cover property (button && $past(digit)==4'hF ##1 (digit==4'd0));
  // Reset followed by a button increment
  cover property ($rose(reset) ##1 (!reset && button));

endmodule

// Bind into the DUT
bind seven_segment_controller seven_segment_controller_sva sva_i (
  .clk   (clk),
  .reset (reset),
  .button(button),
  .digit (digit),
  .leds  (leds)
);