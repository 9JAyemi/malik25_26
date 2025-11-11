// SVA for delay_module
module delay_module_sva (
  input logic        clk,
  input logic        A,
  input logic [3:0]  delay_val,
  input logic        X,
  input logic [3:0]  counter
);

  // Counter must increment by 1 modulo 16 every cycle
  property p_cnt_inc_mod16;
    @(posedge clk)
      !$isunknown($past(counter)) |-> counter == $past(counter) + 4'd1;
  endproperty
  assert property (p_cnt_inc_mod16);

  // Next-cycle X is either held, or sampled from A when counter matches delay_val
  property p_x_next_functional;
    @(posedge clk)
      !$isunknown({$past(counter), $past(delay_val), $past(A), $past(X)}) |->
        X === ( ($past(counter) == $past(delay_val)) ? $past(A) : $past(X) );
  endproperty
  assert property (p_x_next_functional);

  // X only changes on cycles where the previous cycle had counter == delay_val
  property p_x_changes_only_on_match;
    @(posedge clk)
      (!$isunknown({$past(counter), $past(delay_val), $past(X), X}) && $changed(X))
        |-> ($past(counter) == $past(delay_val));
  endproperty
  assert property (p_x_changes_only_on_match);

  // Coverage: see an update event (match), and counter wrap
  cover property (@(posedge clk) (counter == delay_val));
  cover property (@(posedge clk) ($past(counter) == 4'hF && counter == 4'h0));

  // Coverage: observe match at extreme delay values
  cover property (@(posedge clk) (counter == delay_val) && (delay_val == 4'h0));
  cover property (@(posedge clk) (counter == delay_val) && (delay_val == 4'hF));

endmodule

// Bind into the DUT (accesses internal 'counter')
bind delay_module delay_module_sva u_delay_module_sva (
  .clk(clk),
  .A(A),
  .delay_val(delay_val),
  .X(X),
  .counter(counter)
);