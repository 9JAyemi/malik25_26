// Bindable SVA checker for FSM. Focused, high-signal-quality checks and concise coverage.
module FSM_sva;

  // Local sizing
  localparam int W = s + n;

  // Static sanity (elaboration-time) checks
  initial begin
    assert (n >= 4) else $fatal(1, "FSM: parameter n must be >= 4 (uses input_reg[3:0])");
    assert (m >= 2) else $fatal(1, "FSM: parameter m must be >= 2 (drives out[1:0])");
  end

  // No X/Z on key signals and intended 2-bit state encoding in LSBs
  always @* begin
    assert (!$isunknown({state, input_reg, output_wire, out}))
      else $error("FSM: X/Z detected on key signals");
    assert (state[s-1:2] == '0)
      else $error("FSM: upper state bits [%0d:%0d] must be 0", s-1, 2);
  end

  // Output function correctness
  always @* begin
    assert (out === output_wire) else $error("FSM: out must mirror output_wire");
    assert (output_wire[0] === ((state[1:0] == STATE_0) ? (input_reg[0] & input_reg[1])
                                                       : (input_reg[2] | input_reg[3])))
      else $error("FSM: output_wire[0] function mismatch");
    assert (output_wire[1] === ((state[1:0] == STATE_2) ? (input_reg[0] ^ input_reg[1])
                                                       : (input_reg[2] & input_reg[3])))
      else $error("FSM: output_wire[1] function mismatch");
  end

  // input_reg must follow in after NBA update
  always @(in) begin
    automatic logic [n-1:0] in0 = in;
    #0 assert (input_reg == in0) else
      $error("FSM: input_reg failed to capture in (exp=%0h got=%0h)", in0, input_reg);
  end

  // Expected next-state function reflecting the coded case mapping (with width extension)
  function automatic [s-1:0] ns_func (input [s-1:0] cs, input [n-1:0] ir);
    automatic [s-1:0] ns = cs;
    unique case ({cs, ir})
      {{(W-3){1'b0}}, TRANSITION_0}: ns = {{(s-2){1'b0}}, STATE_0};
      {{(W-3){1'b0}}, TRANSITION_1}: ns = {{(s-2){1'b0}}, STATE_1};
      {{(W-3){1'b0}}, TRANSITION_2}: ns = {{(s-2){1'b0}}, STATE_2};
      {{(W-3){1'b0}}, TRANSITION_3}: ns = {{(s-2){1'b0}}, STATE_3};
      {{(W-3){1'b0}}, TRANSITION_4}: ns = {{(s-2){1'b0}}, STATE_0};
      {{(W-3){1'b0}}, TRANSITION_5}: ns = {{(s-2){1'b0}}, STATE_1};
      {{(W-3){1'b0}}, TRANSITION_6}: ns = {{(s-2){1'b0}}, STATE_2};
      {{(W-3){1'b0}}, TRANSITION_7}: ns = {{(s-2){1'b0}}, STATE_3};
      default: /* hold state */;
    endcase
    return ns;
  endfunction

  // Combinational state-update check (delta-cycle compares NBA result to expected)
  always @(state or input_reg) begin
    automatic logic [s-1:0] cs = state;
    automatic logic [n-1:0] ir = input_reg;
    automatic logic [s-1:0] ns = ns_func(cs, ir);
    #0 assert (state == ns)
      else $error("FSM: state transition mismatch exp=%0h got=%0h (cs=%0h ir=%0h)", ns, state, cs, ir);
  end

  // Concise functional coverage (transition guards, states, and output activity)
  always @(state or input_reg or out) begin
    // Each coded transition guard reachable
    cover ({state, input_reg} === {{(W-3){1'b0}}, TRANSITION_0});
    cover ({state, input_reg} === {{(W-3){1'b0}}, TRANSITION_1});
    cover ({state, input_reg} === {{(W-3){1'b0}}, TRANSITION_2});
    cover ({state, input_reg} === {{(W-3){1'b0}}, TRANSITION_3});
    cover ({state, input_reg} === {{(W-3){1'b0}}, TRANSITION_4});
    cover ({state, input_reg} === {{(W-3){1'b0}}, TRANSITION_5});
    cover ({state, input_reg} === {{(W-3){1'b0}}, TRANSITION_6});
    cover ({state, input_reg} === {{(W-3){1'b0}}, TRANSITION_7});

    // Visit all state encodings (LSBs)
    cover (state[1:0] == STATE_0);
    cover (state[1:0] == STATE_1);
    cover (state[1:0] == STATE_2);
    cover (state[1:0] == STATE_3);

    // Output activity
    cover (out[0] == 0); cover (out[0] == 1);
    cover (out[1] == 0); cover (out[1] == 1);
  end

endmodule

// Bind into all FSM instances
bind FSM FSM_sva sva_FSM();