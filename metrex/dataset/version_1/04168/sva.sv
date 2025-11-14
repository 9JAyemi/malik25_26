// SVA checker for state_splitting_FSM
module state_splitting_FSM_sva #(parameter int n=4, m=2) (
  input logic              clk,
  input logic [n-1:0]      in,
  input logic [m-1:0]      out,
  input logic [1:0]        state
);

  // allow one cycle for $past to be valid
  logic started;
  always_ff @(posedge clk) started <= 1'b1;

  // Golden next-state function derived from spec
  function automatic logic [1:0] ns(input logic [1:0] s, input logic i0, input logic i1);
    unique case (s)
      2'b00: ns = (i0 & i1) ? 2'b11 :
                 (i0)       ? 2'b01 :
                 (i1)       ? 2'b10 : 2'b00;
      2'b01: ns = (i0 & i1) ? 2'b11 :
                 (i1)       ? 2'b00 : 2'b01;
      2'b10: ns = (i0 & i1) ? 2'b11 :
                 (i0)       ? 2'b00 : 2'b10;
      2'b11: ns = (!i0 & !i1) ? 2'b00 :
                 (!i0)        ? 2'b10 :
                 (!i1)        ? 2'b01 : 2'b11;
      default: ns = 2'b00;
    endcase
  endfunction

  // State transition correctness: state(t+1) == ns(state(t), in[1:0](t))
  property p_state_update;
    @(posedge clk) disable iff (!started)
      state == ns($past(state), $past(in[0]), $past(in[1]));
  endproperty
  assert property (p_state_update);

  // Output is purely a decode of state: out[0]=state[1], out[1]=state[0]
  assert property (@(posedge clk) {out[1],out[0]} == {state[0],state[1]});

  // No mid-cycle glitches on outputs (sample at negedge)
  assert property (@(negedge clk) $stable(out));

  // Sanity: no X/Z on key signals after startup
  assert property (@(posedge clk) disable iff (!started)
                   !$isunknown(state) && !$isunknown(out));

  // Functional coverage: hit all states
  cover property (@(posedge clk) state == 2'b00);
  cover property (@(posedge clk) state == 2'b01);
  cover property (@(posedge clk) state == 2'b10);
  cover property (@(posedge clk) state == 2'b11);

  // Functional coverage: hit every (state, in[1:0]) -> next_state transition
`define COV(s,i,ns_) cover property (@(posedge clk) disable iff (!started) \
                        ($past(state)==(s) && $past(in[1:0])==(i)) ##1 (state==(ns_)));

  // From 00
  `COV(2'b00, 2'b00, 2'b00)
  `COV(2'b00, 2'b01, 2'b10)
  `COV(2'b00, 2'b10, 2'b01)
  `COV(2'b00, 2'b11, 2'b11)

  // From 01
  `COV(2'b01, 2'b00, 2'b01)
  `COV(2'b01, 2'b01, 2'b01)
  `COV(2'b01, 2'b10, 2'b00)
  `COV(2'b01, 2'b11, 2'b11)

  // From 10
  `COV(2'b10, 2'b00, 2'b10)
  `COV(2'b10, 2'b01, 2'b00)
  `COV(2'b10, 2'b10, 2'b10)
  `COV(2'b10, 2'b11, 2'b11)

  // From 11
  `COV(2'b11, 2'b00, 2'b00)
  `COV(2'b11, 2'b01, 2'b01)
  `COV(2'b11, 2'b10, 2'b10)
  `COV(2'b11, 2'b11, 2'b11)

`undef COV

endmodule

// Bind the checker to the DUT (accesses internal 'state')
bind state_splitting_FSM state_splitting_FSM_sva #(.n(n), .m(m))
  state_splitting_FSM_sva_i(.clk(clk), .in(in), .out(out), .state(state));