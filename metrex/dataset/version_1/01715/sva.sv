// SVA for FSM: checks legal states, registered update, functional transition map,
// output decode/onehot, X-checks, and full transition coverage. Also flags
// missing state in next_state sensitivity via a combinational consistency check.

module FSM_SVA #(
  parameter int n = 4,
  parameter int m = 2
)(
  input  logic              clk,
  input  logic [m-1:0]      in,
  input  logic [n-1:0]      out,
  input  logic [n-1:0]      state,
  input  logic [n-1:0]      next_state
);

  // Parameter sanity (this DUT hardcodes a 4-state, 2-input FSM)
  initial begin
    if (!(n==4 && m==2)) $error("FSM_SVA assumes n==4 and m==2");
  end

  // Clocking / init gate to skip time-0
  logic init;
  initial init = 1'b0;
  always_ff @(posedge clk) init <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!init)

  // Functional spec of the next-state map
  function automatic logic [n-1:0] f_next(input logic [n-1:0] s, input logic [m-1:0] i);
    logic [n-1:0] ns;
    unique case (s)
      0: ns = (i[0] && i[1]) ? 3 : (i[0] ? 1 : (i[1] ? 2 : 0));
      1: ns = (i[0] && i[1]) ? 3 : (          i[1] ? 2 : 0);
      2: ns = (i[0] && i[1]) ? 3 : (i[0] ? 1 :           0);
      3: ns = (i[0] && i[1]) ? 3 : (i[0] ? 1 : (i[1] ? 2 : 0));
      default: ns = 'x;
    endcase
    return ns;
  endfunction

  // No X/Z on key signals
  assert property (!$isunknown({in[1:0], state[1:0], next_state[1:0], out})))
    else $error("X/Z detected on in/state/next_state/out");

  // Legal state encoding (0..3)
  assert property (state inside {[0:3]})
    else $error("Illegal state encoding: %0d", state);

  // Output is one-hot and decodes state as 1 << state
  assert property ($onehot(out))
    else $error("Output not one-hot: %b", out);

  assert property (out == (4'b0001 << state[1:0]))
    else $error("Output decode mismatch: state=%0d out=%b", state, out);

  // Registered update: state picks up prior cycle's next_state
  assert property (state == $past(next_state))
    else $error("Sequential update mismatch: state != $past(next_state)");

  // Functional transition: state' == f(state,in) using prior-cycle inputs/state
  assert property (state == f_next($past(state), $past(in)))
    else $error("Functional transition mismatch: prev(state,in) -> state");

  // Combinational correctness: next_state should equal f(state,in) at sample time
  // This will flag the missing 'state' in the next_state sensitivity list.
  assert property (next_state == f_next(state, in))
    else $error("Combinational next_state mismatch vs f(state,in)");

  // Coverage: reach all states and all state/input -> next-state transitions
  genvar I, K;
  generate
    for (I = 0; I < 4; I++) begin : COV_ST
      cover property (state == I);
      for (K = 0; K < 4; K++) begin : COV_TR
        cover property (($past(state) == I && $past(in) == K) ##1
                         state == f_next(I[K:K], K)); // cast fine; f_next handles widths
      end
    end
  endgenerate

endmodule

// Bind into the DUT
bind FSM FSM_SVA #(.n(n), .m(m)) fsm_sva_i (.*);