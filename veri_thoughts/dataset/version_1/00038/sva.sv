// SVA checker for FSM. Bind to the DUT to verify next-state/output logic and cover all paths.

module fsm_sva #(parameter int n=4, m=2, s=8)
(
  input  logic [n-1:0] in,
  input  logic [m-1:0] out,
  input  logic [s-1:0] state
);

  // Fire assertions when inputs change (matches DUT sensitivity)
  event in_ev;
  always @(in) -> in_ev;

  // Sanity on params
  initial begin
    if (n < 4) $error("FSM SVA: n must be >= 4");
    if (m != 2) $error("FSM SVA: m must be 2");
    if (s < 3) $error("FSM SVA: s must be >= 3");
  end

  // Expected next-state and output functions (per RTL)
  function automatic logic [2:0] ns3 (input logic [2:0] st, input logic [n-1:0] i);
    case (st)
      3'b000: ns3 = (i[0] && i[1]) ? 3'b001 :
                    (i[2])         ? 3'b010 : 3'b000;
      3'b001: ns3 = (i[0] && i[1]) ? 3'b001 :
                    (i[2])         ? 3'b011 : 3'b000;
      3'b010: ns3 = (i[0] && i[1]) ? 3'b011 :
                    (i[2])         ? 3'b010 : 3'b000;
      3'b011: ns3 = (i[0] && i[1]) ? 3'b011 :
                    (i[2])         ? 3'b010 : 3'b001;
      3'b100: ns3 = (i[1] && i[3]) ? 3'b101 :
                    (i[0])         ? 3'b110 : 3'b100;
      3'b101: ns3 = (i[1] && i[3]) ? 3'b101 :
                    (i[0])         ? 3'b111 : 3'b100;
      3'b110: ns3 = (i[1] && i[3]) ? 3'b111 :
                    (i[0])         ? 3'b110 : 3'b100;
      3'b111: ns3 = (i[1] && i[3]) ? 3'b111 :
                    (i[0])         ? 3'b110 : 3'b101;
      default: ns3 = st;
    endcase
  endfunction

  function automatic logic [1:0] no3 (input logic [2:0] st, input logic [n-1:0] i);
    case (st)
      3'b000,3'b001,3'b010,3'b011:
        no3 = (i[0] && i[1]) ? 2'b10 :
              (i[2])         ? 2'b01 : 2'b00;
      3'b100,3'b101,3'b110,3'b111:
        no3 = (i[1] && i[3]) ? 2'b10 :
              (i[0])         ? 2'b01 : 2'b00;
      default: no3 = 2'b00;
    endcase
  endfunction

  // Legal state encoding: upper bits must be 0
  generate if (s > 3) begin
    assert property (@(in_ev) ##0 (state[s-1:3] == '0))
      else $error("FSM: upper state bits must remain 0");
  end endgenerate

  // Output encoding only allows 00/01/10
  assert property (@(in_ev) ##0 (out inside {2'b00,2'b01,2'b10}))
    else $error("FSM: out has illegal value");

  // Core functional check: after an input change, state/out match RTL mapping (NBA-aware)
  assert property (@(in_ev) 1 |-> ##0
                   (state[2:0] == ns3($past(state[2:0],0), in) &&
                    out        == no3($past(state[2:0],0), in)))
    else $error("FSM: next-state/output mismatch");

  // Hold-path stability checks
  assert property (@(in_ev)
                   ($past(state[2:0],0) inside {3'b000,3'b001,3'b010,3'b011} &&
                    !(in[0]&&in[1]) && !in[2]) |-> ##0 $stable(state[2:0]))
    else $error("FSM: unexpected state change in 0..3 hold path");

  assert property (@(in_ev)
                   ($past(state[2:0],0) inside {3'b100,3'b101,3'b110,3'b111} &&
                    !(in[1]&&in[3]) && !in[0]) |-> ##0 $stable(state[2:0]))
    else $error("FSM: unexpected state change in 4..7 hold path");

  // Coverage: visit all states and outputs
  genvar k;
  for (k=0; k<8; k++) begin : C_STATES
    cover property (@(in_ev) ##0 state[2:0] == k[2:0]);
  end
  cover property (@(in_ev) ##0 out==2'b00);
  cover property (@(in_ev) ##0 out==2'b01);
  cover property (@(in_ev) ##0 out==2'b10);

  // Coverage: all branches/transitions
  // 0-group
  cover property (@(in_ev) ($past(state[2:0],0)==3'b000 &&  in[0]&&in[1]) ##0 (state[2:0]==3'b001 && out==2'b10));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b000 && !(in[0]&&in[1]) &&  in[2]) ##0 (state[2:0]==3'b010 && out==2'b01));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b000 && !(in[0]&&in[1]) && !in[2]) ##0 (state[2:0]==3'b000 && out==2'b00));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b001 &&  in[0]&&in[1]) ##0 (state[2:0]==3'b001 && out==2'b10));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b001 && !(in[0]&&in[1]) &&  in[2]) ##0 (state[2:0]==3'b011 && out==2'b01));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b001 && !(in[0]&&in[1]) && !in[2]) ##0 (state[2:0]==3'b000 && out==2'b00));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b010 &&  in[0]&&in[1]) ##0 (state[2:0]==3'b011 && out==2'b10));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b010 && !(in[0]&&in[1]) &&  in[2]) ##0 (state[2:0]==3'b010 && out==2'b01));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b010 && !(in[0]&&in[1]) && !in[2]) ##0 (state[2:0]==3'b000 && out==2'b00));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b011 &&  in[0]&&in[1]) ##0 (state[2:0]==3'b011 && out==2'b10));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b011 && !(in[0]&&in[1]) &&  in[2]) ##0 (state[2:0]==3'b010 && out==2'b01));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b011 && !(in[0]&&in[1]) && !in[2]) ##0 (state[2:0]==3'b001 && out==2'b00));
  // 4-group
  cover property (@(in_ev) ($past(state[2:0],0)==3'b100 &&  in[1]&&in[3]) ##0 (state[2:0]==3'b101 && out==2'b10));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b100 && !(in[1]&&in[3]) &&  in[0]) ##0 (state[2:0]==3'b110 && out==2'b01));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b100 && !(in[1]&&in[3]) && !in[0]) ##0 (state[2:0]==3'b100 && out==2'b00));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b101 &&  in[1]&&in[3]) ##0 (state[2:0]==3'b101 && out==2'b10));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b101 && !(in[1]&&in[3]) &&  in[0]) ##0 (state[2:0]==3'b111 && out==2'b01));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b101 && !(in[1]&&in[3]) && !in[0]) ##0 (state[2:0]==3'b100 && out==2'b00));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b110 &&  in[1]&&in[3]) ##0 (state[2:0]==3'b111 && out==2'b10));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b110 && !(in[1]&&in[3]) &&  in[0]) ##0 (state[2:0]==3'b110 && out==2'b01));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b110 && !(in[1]&&in[3]) && !in[0]) ##0 (state[2:0]==3'b100 && out==2'b00));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b111 &&  in[1]&&in[3]) ##0 (state[2:0]==3'b111 && out==2'b10));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b111 && !(in[1]&&in[3]) &&  in[0]) ##0 (state[2:0]==3'b110 && out==2'b01));
  cover property (@(in_ev) ($past(state[2:0],0)==3'b111 && !(in[1]&&in[3]) && !in[0]) ##0 (state[2:0]==3'b101 && out==2'b00));

endmodule

// Bind into the DUT scope; connects to internal 'state' reg
bind FSM fsm_sva #(.n(n), .m(m), .s(s)) i_fsm_sva (.*);