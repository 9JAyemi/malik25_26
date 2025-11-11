// SVA checkers for bit_converter and byte_to_bit_converter
// Concise functional checks, X-protection when used, and basic coverage.

module bit_converter_sva(input bit_in, input strobe, input clk, input bit_out);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Core behavior: load on strobe, else hold (1-cycle relation)
  property p_load_hold;
    @(posedge clk) disable iff (!past_valid)
      bit_out == ($past(strobe) ? $past(bit_in) : $past(bit_out));
  endproperty
  assert property (p_load_hold);

  // Must not change when strobe was low
  assert property (@(posedge clk) disable iff (!past_valid)
                   !$past(strobe) |-> $stable(bit_out));

  // Inputs must be known when used; strobe should be known
  assert property (@(posedge clk) strobe |-> !$isunknown(bit_in));
  assert property (@(posedge clk) !$isunknown(strobe));

  // After a capture, output becomes known by next cycle
  assert property (@(posedge clk) disable iff (!past_valid)
                   $rose(strobe) |-> ##1 !$isunknown(bit_out));

  // Coverage: capture both 0 and 1; observe output toggle
  cover property (@(posedge clk) strobe && (bit_in==1'b0));
  cover property (@(posedge clk) strobe && (bit_in==1'b1));
  cover property (@(posedge clk) $changed(bit_out));
endmodule

module byte_to_bit_converter_sva(input [7:0] byte_in, input strobe, input clk, input [7:0] bit_out);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Vector equivalence of eight independent bit converters
  assert property (@(posedge clk) disable iff (!past_valid)
                   bit_out == ($past(strobe) ? $past(byte_in) : $past(bit_out)));

  // Must not change when strobe was low
  assert property (@(posedge clk) disable iff (!past_valid)
                   !$past(strobe) |-> $stable(bit_out));

  // Inputs must be known when used; strobe should be known
  assert property (@(posedge clk) strobe |-> !$isunknown(byte_in));
  assert property (@(posedge clk) !$isunknown(strobe));

  // Coverage: capture all-0s, all-1s, and mixed patterns; observe output toggle
  cover property (@(posedge clk) strobe && (byte_in==8'h00));
  cover property (@(posedge clk) strobe && (byte_in==8'hFF));
  cover property (@(posedge clk) strobe && ($countones(byte_in) inside {[1:7]}));
  cover property (@(posedge clk) $changed(bit_out));
endmodule

// Bind into DUTs
bind bit_converter         bit_converter_sva         u_bit_converter_sva       (.bit_in(bit_in), .strobe(strobe), .clk(clk), .bit_out(bit_out));
bind byte_to_bit_converter byte_to_bit_converter_sva u_byte_to_bit_converter_sva(.byte_in(byte_in), .strobe(strobe), .clk(clk), .bit_out(bit_out));