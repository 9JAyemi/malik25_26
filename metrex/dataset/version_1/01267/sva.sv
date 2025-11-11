// SVA for up_down_counter
module up_down_counter_sva (
  input clk,
  input up_down,
  input reset,
  input [3:0] out
);
  default clocking cb @(posedge clk); endclocking

  // past-valid guard
  logic past_valid; initial past_valid = 0; always @(posedge clk) past_valid <= 1;

  // 4-bit wrap helpers
  function automatic logic [3:0] add1(input logic [3:0] v); add1 = v + 4'd1; endfunction
  function automatic logic [3:0] sub1(input logic [3:0] v); sub1 = v - 4'd1; endfunction

  // Clean inputs at sample
  assert property ( !$isunknown({reset, up_down}) );

  // Reset behavior (synchronous)
  assert property ( reset |=> out == 4'h0 );

  // Functional next-state checks (use previous cycle's direction)
  assert property ( past_valid && !$past(reset) && !reset &&  $past(up_down) |-> out == add1($past(out)) );
  assert property ( past_valid && !$past(reset) && !reset && !$past(up_down) |-> out == sub1($past(out)) );

  // Must change every cycle when not in reset
  assert property ( past_valid && !$past(reset) && !reset |-> out != $past(out) );

  // No X on out when active
  assert property ( !reset |-> !$isunknown(out) );

  // Coverage
  cover property ( reset ##1 !reset ); // saw a reset pulse
  cover property ( past_valid && !$past(reset) && !reset &&  $past(up_down) && ($past(out)==4'hF) && (out==4'h0) ); // up wrap
  cover property ( past_valid && !$past(reset) && !reset && !$past(up_down) && ($past(out)==4'h0) && (out==4'hF) ); // down wrap
  cover property ( $rose(up_down) );
  cover property ( $fell(up_down) );
endmodule

// Bind into DUT
bind up_down_counter up_down_counter_sva u_up_down_counter_sva (
  .clk(clk), .up_down(up_down), .reset(reset), .out(out)
);