// SVA for FSM: bind into the DUT. Focused, high-quality checks and coverage.

bind FSM FSM_sva #(.n(n), .m(m)) u_fsm_sva();

module FSM_sva #(parameter int n=4, m=2) ();
  // Implicit access to DUT scope: clk, in, out, state, next_state, S0..S7

  default clocking cb @(posedge clk); endclocking

  // Sanity on parameters
  initial begin
    assert (n >= 4) else $error("FSM SVA: n (%0d) must be >= 4", n);
    assert (m == 2) else $error("FSM SVA: m (%0d) must be exactly 2", m);
  end

  // Golden next-state function
  function automatic logic [2:0] ns_func (input logic [2:0] s, input logic [n-1:0] din);
    case (s)
      S0: ns_func = din[0] ? S1 : S0;
      S1: ns_func = din[1] ? S3 : S2;
      S2: ns_func = din[2] ? S3 : S1;
      S3: ns_func = din[3] ? S4 : S0;
      S4: ns_func = din[0] ? S5 : S4;
      S5: ns_func = din[1] ? S7 : S6;
      S6: ns_func = din[2] ? S7 : S5;
      S7: ns_func = din[3] ? S0 : S4;
      default: ns_func = 'x;
    endcase
  endfunction

  // Combinational next_state mapping holds at sample times
  assert property ( !$isunknown({state,in}) |-> next_state == ns_func(state,in) );

  // Sequential state update equals golden mapping
  assert property ( !$isunknown($past(state)) && !$isunknown($past(in))
                    |-> state == ns_func($past(state), $past(in)) );

  // Output correctness and one-hotness
  assert property ( !$isunknown(state) |-> {out[1],out[0]} == {state[2], ~state[2]} );
  assert property ( out[0] ^ out[1] );

  // State reachability coverage
  cover property ( state == S0 );
  cover property ( state == S1 );
  cover property ( state == S2 );
  cover property ( state == S3 );
  cover property ( state == S4 );
  cover property ( state == S5 );
  cover property ( state == S6 );
  cover property ( state == S7 );

  // Transition coverage (both branches from each state)
  cover property ( $past(state)==S0 &&  $past(in[0]) ##1 state==S1 );
  cover property ( $past(state)==S0 && !$past(in[0]) ##1 state==S0 );
  cover property ( $past(state)==S1 &&  $past(in[1]) ##1 state==S3 );
  cover property ( $past(state)==S1 && !$past(in[1]) ##1 state==S2 );
  cover property ( $past(state)==S2 &&  $past(in[2]) ##1 state==S3 );
  cover property ( $past(state)==S2 && !$past(in[2]) ##1 state==S1 );
  cover property ( $past(state)==S3 &&  $past(in[3]) ##1 state==S4 );
  cover property ( $past(state)==S3 && !$past(in[3]) ##1 state==S0 );
  cover property ( $past(state)==S4 &&  $past(in[0]) ##1 state==S5 );
  cover property ( $past(state)==S4 && !$past(in[0]) ##1 state==S4 );
  cover property ( $past(state)==S5 &&  $past(in[1]) ##1 state==S7 );
  cover property ( $past(state)==S5 && !$past(in[1]) ##1 state==S6 );
  cover property ( $past(state)==S6 &&  $past(in[2]) ##1 state==S7 );
  cover property ( $past(state)==S6 && !$past(in[2]) ##1 state==S5 );
  cover property ( $past(state)==S7 &&  $past(in[3]) ##1 state==S0 );
  cover property ( $past(state)==S7 && !$past(in[3]) ##1 state==S4 );

  // Output-domain crossing coverage (half-to-half)
  cover property ( $past(out)==2'b01 && out==2'b10 );
  cover property ( $past(out)==2'b10 && out==2'b01 );
endmodule