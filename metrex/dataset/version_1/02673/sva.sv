// Bindable SVA checker for FSM_split
module FSM_split_sva;
  // This checker is meant to be bind-ed into FSM_split; it can see DUT names directly.
  default clocking cb @(posedge clk); endclocking

  // Original FSM next-state function (concise, single check)
  property p_state_next;
    !$initstate |-> state ==
      (($past(state)==STATE0 && $past(in)==4'b0000) ? STATE1 :
       ($past(state)==STATE1 && $past(in)==4'b0001) ? STATE2 :
       ($past(state)==STATE2 && $past(in)==4'b0010) ? STATE3 :
       ($past(state)==STATE3 && $past(in)==4'b0011) ? STATE4 :
       ($past(state)==STATE4 && $past(in)==4'b0100) ? STATE5 :
       ($past(state)==STATE5 && $past(in)==4'b0101) ? STATE6 :
       ($past(state)==STATE6 && $past(in)==4'b0110) ? STATE7 :
       ($past(state)==STATE7 && $past(in)==4'b0111) ? STATE0 :
       STATE0);
  endproperty
  assert property (p_state_next);

  // Split encoding must compress to {0, LSB of state} (due to the subtraction on 2-bit slice)
  assert property (!$initstate |-> state1 == {1'b0, $past(state[0])});
  assert property (state1 inside {2'b00,2'b01}); // unreachable encodings must never occur

  // Smaller FSM next-state function
  property p_state2_next;
    !$initstate |->
      state2 ==
        (($past(state1)==2'b00) ? (($past(in)==4'b0000) ? 2'b01 : 2'b00) :
         ($past(state1)==2'b01) ? (($past(in)==4'b0001) ? 2'b10 : 2'b00) :
         $past(state2)); // 10/11 unreachable by assertion above; would hold value otherwise
  endproperty
  assert property (p_state2_next);

  // Output function connectivity
  assert property (out == {state2[1], state2[0]});

  // Unreachable/illegal observables
  assert property (state2 != 2'b11);

  // Coverage: walk through all original states and wrap
  cover property (state==STATE0 ##1 state==STATE1 ##1 state==STATE2 ##1 state==STATE3
                  ##1 state==STATE4 ##1 state==STATE5 ##1 state==STATE6 ##1 state==STATE7 ##1 state==STATE0);

  // Coverage: observe split encodings and state2 values that should be reachable
  cover property (state1==2'b00);
  cover property (state1==2'b01);
  cover property (state2==2'b00);
  cover property (state2==2'b01);
  cover property (state2==2'b10);

  // Coverage: demonstrate "reset-to-STATE0 on mismatch" from a mid state
  cover property (state==STATE3 && in!=4'b0011 ##1 state==STATE0);
endmodule

// Bind this checker into the DUT
bind FSM_split FSM_split_sva sva_inst();