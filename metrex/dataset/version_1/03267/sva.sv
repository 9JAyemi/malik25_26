// SVA for clock_generator
// Bind this checker to the DUT
module clock_generator_sva (
  input  logic       clk_in,
  input  logic       reset,
  input  logic       clk_out_1,
  input  logic       clk_out_2,
  input  logic [1:0] count
);

  // Asynchronous reset drives state to zero immediately
  property p_async_reset_state;
    @(posedge reset) ##0 (count==2'b00 && clk_out_1==1'b0 && clk_out_2==1'b0);
  endproperty
  assert property (p_async_reset_state);

  // While reset is asserted, hold zeros
  property p_hold_during_reset;
    @(posedge clk_in) reset |-> (count==2'b00 && clk_out_1==1'b0 && clk_out_2==1'b0);
  endproperty
  assert property (p_hold_during_reset);

  // Count next-state function (ignore cycles around reset)
  property p_count_next;
    @(posedge clk_in)
      disable iff (reset || $past(reset))
      count == (($past(count)==2'b10) ? 2'b00 : $past(count)+2'b01);
  endproperty
  assert property (p_count_next);

  // Count never reaches 2'b11
  property p_count_never_11;
    @(posedge clk_in) disable iff (reset) count != 2'b11;
  endproperty
  assert property (p_count_never_11);

  // clk_out_1 toggles only when prior count==01; otherwise holds
  property p_clk1_toggle_on_01;
    @(posedge clk_in)
      disable iff (reset || $past(reset))
      ($past(count)==2'b01) |-> (clk_out_1 == ~$past(clk_out_1) && clk_out_2 == $past(clk_out_2));
  endproperty
  assert property (p_clk1_toggle_on_01);

  property p_clk1_stable_else;
    @(posedge clk_in)
      disable iff (reset || $past(reset))
      ($past(count)!=2'b01) |-> (clk_out_1 == $past(clk_out_1));
  endproperty
  assert property (p_clk1_stable_else);

  // clk_out_2 toggles only when prior count==10; otherwise holds
  property p_clk2_toggle_on_10;
    @(posedge clk_in)
      disable iff (reset || $past(reset))
      ($past(count)==2'b10) |-> (clk_out_2 == ~$past(clk_out_2) && clk_out_1 == $past(clk_out_1));
  endproperty
  assert property (p_clk2_toggle_on_10);

  property p_clk2_stable_else;
    @(posedge clk_in)
      disable iff (reset || $past(reset))
      ($past(count)!=2'b10) |-> (clk_out_2 == $past(clk_out_2));
  endproperty
  assert property (p_clk2_stable_else);

  // Never toggle both outputs in the same clk_in edge
  property p_mutex_toggles;
    @(posedge clk_in)
      disable iff (reset || $past(reset))
      !((clk_out_1 ^ $past(clk_out_1)) && (clk_out_2 ^ $past(clk_out_2)));
  endproperty
  assert property (p_mutex_toggles);

  // Coverage
  cover property (@(posedge clk_in) disable iff (reset)
                  (count==2'b00) ##1 (count==2'b01) ##1 (count==2'b10) ##1 (count==2'b00));
  cover property (@(posedge clk_in) disable iff (reset || $past(reset))
                  ($past(count)==2'b01) && (clk_out_1 != $past(clk_out_1)));
  cover property (@(posedge clk_in) disable iff (reset || $past(reset))
                  ($past(count)==2'b10) && (clk_out_2 != $past(clk_out_2)));
  cover property (@(posedge reset) ##0 (count==2'b00 && clk_out_1==1'b0 && clk_out_2==1'b0));

endmodule

bind clock_generator clock_generator_sva sva_i (.*);