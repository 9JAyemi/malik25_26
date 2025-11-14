// SVA for LedCounter + Digit
// Bind these checkers to the DUTs. Focused, high-signal-coverage, concise.

package ledcounter_sva_pkg;
  function automatic logic [7:0] segmap(input logic [3:0] d);
    case (d)
      4'h0: segmap = ~8'b11111100;
      4'h1: segmap = ~8'b01100000;
      4'h2: segmap = ~8'b11011010;
      4'h3: segmap = ~8'b11110010;
      4'h4: segmap = ~8'b01100110;
      4'h5: segmap = ~8'b10110110;
      4'h6: segmap = ~8'b10111110;
      4'h7: segmap = ~8'b11100000;
      4'h8: segmap = ~8'b11111110;
      4'h9: segmap = ~8'b11110110;
      4'hA: segmap = ~8'b11101110;
      4'hB: segmap = ~8'b00111110;
      4'hC: segmap = ~8'b10011100;
      4'hD: segmap = ~8'b01111010;
      4'hE: segmap = ~8'b10011110;
      4'hF: segmap = ~8'b10001110;
    endcase
  endfunction

  function automatic logic [3:0] enmask(input logic [6:0] c);
    enmask = (c[4] == 1'b0) ? ~(4'b0001 << c[6:5]) : 4'hF;
  endfunction
endpackage


module LedCounter_sva;
  import ledcounter_sva_pkg::*;

  // Clocks for assertions
  default clocking cb_clk @(posedge clk); endclocking
  clocking cb_wr @(posedge write); endclocking

  // Counter increments by exactly 1 every clk
  property p_counter_inc;
    !$isunknown($past(counter)) |-> counter == $past(counter) + 7'd1;
  endproperty
  assert property (cb_clk.p_counter_inc);

  // Enable mask matches counter decode; inactive when counter[4]==1
  assert property (cb_clk (enable_segments == enmask(counter)));
  assert property (cb_clk (counter[4] == 1) |-> (enable_segments == 4'hF));
  assert property (cb_clk (counter[4] == 0) |-> $onehot(~enable_segments));

  // Displayed segments correspond to selected digit value
  assert property (cb_clk (segments == segmap(digits[counter[6:5]])));

  // Writes: when enable=1, digits update to data_bus nibbles on write edge (NBA)
  property p_write_updates;
    enable && !$isunknown(data_bus) |-> ##0
      (digits[0] == $past(data_bus[3:0])   &&
       digits[1] == $past(data_bus[7:4])   &&
       digits[2] == $past(data_bus[11:8])  &&
       digits[3] == $past(data_bus[15:12]));
  endproperty
  assert property (cb_wr.p_write_updates);

  // Writes: when enable=0, digits hold
  property p_write_no_update;
    !enable |-> ##0
      (digits[0] == $past(digits[0]) &&
       digits[1] == $past(digits[1]) &&
       digits[2] == $past(digits[2]) &&
       digits[3] == $past(digits[3]));
  endproperty
  assert property (cb_wr.p_write_no_update);

  // No X/Z on outputs; bus must be known when sampled for write
  assert property (cb_clk (!$isunknown(segments) && !$isunknown(enable_segments)));
  assert property (cb_wr (enable |-> !$isunknown(data_bus)));

  // Cross-consistency: when counter[4]==0, enable mask equals ~(1<<index)
  assert property (cb_clk (counter[4]==0) |-> (enable_segments == ~(4'b0001 << counter[6:5])));

  // Coverage

  // Counter wrap
  cover property (cb_clk ($past(counter)==7'h7F && counter==7'h00));

  // Each digit position gets enabled
  genvar i;
  generate
    for (i=0; i<4; i++) begin : C_EN_POS
      cover property (cb_clk (counter[4]==0 && counter[6:5]==i[1:0] &&
                              enable_segments == ~(4'b0001 << i)));
    end
  endgenerate

  // Observe all 16 segment codes on output at some time
  genvar v;
  generate
    for (v=0; v<16; v++) begin : C_SEG_CODES
      cover property (cb_clk (segments == segmap(v[3:0])));
    end
  endgenerate

  // Write with enable and without
  cover property (cb_wr enable);
  cover property (cb_wr !enable);

endmodule

bind LedCounter LedCounter_sva;


// Optional: direct Digit mapping check (bind to submodule)
module Digit_sva;
  import ledcounter_sva_pkg::*;
  // Sample on any activity of digit or output via a free-running check at clk edges if available
  // Use concurrent check on implicit combinational relationship at edges of real_segments
  assert property (@(posedge $global_clock) real_segments == segmap(digit))
    else $error("Digit mapping mismatch");
  // If no global clock is available in your environment, you can alternatively:
  // assert property (@(real_segments or digit) real_segments == segmap(digit));
endmodule

bind Digit Digit_sva;