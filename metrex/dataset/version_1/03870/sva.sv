// SVA for divider; bind this to the DUT
module divider_sva
  #(parameter int divisor1 = 5, divisor2 = 2)
  (input  logic        clk,
   input  logic        reset,      // active-low async in DUT
   input  logic        out,
   input  logic [31:0] cnt1,
   input  logic        result,
   input  logic        EN,
   input  logic        compare1,
   input  logic        compare2);

  // Reset behavior (check during reset low)
  // While reset is asserted low, cnt1/result must be held at 0
  assert property (@(posedge clk) !reset |-> (cnt1==32'd0 && result==1'b0));

  // On deassertion of reset, first active clock produces cnt1 == 1
  assert property (@(posedge clk) $rose(reset) |=> (cnt1==32'd1));

  // Counter next-state and range (post-reset)
  assert property (@(posedge clk) disable iff (!reset)
                   $past(reset) |-> cnt1 == (($past(cnt1)==divisor1) ? 32'd1 : $past(cnt1)+32'd1));

  assert property (@(posedge clk) disable iff (!reset)
                   $past(reset) |-> (cnt1 >= 32'd1 && cnt1 <= divisor1));

  // Combinational signal correctness
  assert property (@(posedge clk) compare1 == (cnt1 == divisor1));
  assert property (@(posedge clk) compare2 == (cnt1 == divisor2));
  assert property (@(posedge clk) EN == (compare1 || compare2));
  assert property (@(posedge clk) out == result);

  // Overlap only if divisors equal
  assert property (@(posedge clk) (compare1 && compare2) |-> (divisor1 == divisor2));

  // Result toggles iff EN was 1 in preceding cycle (post-reset)
  assert property (@(posedge clk) disable iff (!reset)
                   $past(reset) |-> ((result ^ $past(result)) == $past(EN)));

  // No X/Z on key outputs when out of reset
  assert property (@(posedge clk) disable iff (!reset)
                   !$isunknown({cnt1, result, out, EN, compare1, compare2}));

  // Coverage
  cover property (@(posedge clk) $rose(reset));
  cover property (@(posedge clk) compare1);
  cover property (@(posedge clk) compare2);
  cover property (@(posedge clk) EN);
  cover property (@(posedge clk) (compare1 && compare2));                // only if thresholds coincide
  cover property (@(posedge clk) disable iff (!reset)
                  ($past(cnt1)==divisor1 && cnt1==32'd1));               // rollover
  cover property (@(posedge clk) disable iff (!reset)
                  ($past(EN) && (result != $past(result))));             // observed toggle
endmodule

// Bind into DUT (inherits DUT parameters and connects to internals by name)
bind divider divider_sva #(.divisor1(divisor1), .divisor2(divisor2)) u_divider_sva (.*);