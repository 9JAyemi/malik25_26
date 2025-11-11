// SVA for counter
module counter_sva (
  input clk,
  input thresh_sw,
  input count_sw,
  input [31:0] threshold,
  input [31:0] count,
  input zero,
  input max,
  input gtu, input gts,
  input ltu, input lts,
  input geu, input ges,
  input leu, input les
);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Next-state of count (priority: count_sw > thresh_sw > increment)
  assert property ($past(count_sw) |-> count == 32'd0);
  assert property ($past(!count_sw && thresh_sw) |-> count == $past(count) - 32'd1);
  assert property ($past(!count_sw && !thresh_sw) |-> count == $past(count) + 32'd1);

  // Flag correctness (flags reflect pre-update count/threshold)
  assert property (zero == ($past(count) == 32'd0));
  assert property (max  == ($past(count) == 32'hFFFF_FFFF));

  assert property (gtu == ($past(count) >  $past(threshold)));
  assert property (ltu == ($past(count) <  $past(threshold)));
  assert property (geu == ($past(count) >= $past(threshold)));
  assert property (leu == ($past(count) <= $past(threshold)));

  assert property (gts == ($signed($past(count)) >  $signed($past(threshold))));
  assert property (lts == ($signed($past(count)) <  $signed($past(threshold))));
  assert property (ges == ($signed($past(count)) >= $signed($past(threshold))));
  assert property (les == ($signed($past(count)) <= $signed($past(threshold))));

  // Cross-consistency among outputs
  assert property (geu == !ltu);
  assert property (leu == !gtu);
  assert property (ges == !lts);
  assert property (les == !gts);

  // Equality corner-case behavior
  assert property (($past(count) == $past(threshold)) |->
                   (!gtu && !ltu && geu && leu && !gts && !lts && ges && les));

  // Coverage
  cover property ($past(count_sw));                      // reset path
  cover property ($past(thresh_sw && !count_sw));        // decrement path
  cover property ($past(!count_sw && !thresh_sw));       // increment path
  cover property ($past(count_sw && thresh_sw));         // priority case

  cover property ($past(count) == 32'hFFFF_FFFF &&
                  $past(!count_sw && !thresh_sw) && count == 32'd0);          // inc wrap
  cover property ($past(count) == 32'd0 &&
                  $past(thresh_sw && !count_sw) && count == 32'hFFFF_FFFF);   // dec wrap

  cover property ($past(count) == $past(threshold));     // equality compare case
  cover property ((gtu ^ gts) || (ltu ^ lts));           // signed vs unsigned differ
endmodule

bind counter counter_sva i_counter_sva (.*);