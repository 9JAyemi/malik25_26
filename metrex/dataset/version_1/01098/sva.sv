// SVA for FSM. Bind this file to the DUT.
// Focus: state encoding correctness, next-state function, and output function.
// Concise, full functional checks plus coverage.

module fsm_sva #(parameter int n=4, m=2) (
  input logic              clk,
  input logic [n-1:0]      in,
  input logic [m-1:0]      out,
  input logic [7:0]        state
);

  // Past-valid to safely use $past
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Helpers
  function automatic logic [2:0] nxt10 (input logic [2:0] s);
    case (s)
      3'd0: nxt10 = 3'd1;
      3'd1: nxt10 = 3'd3;
      3'd2: nxt10 = 3'd0;
      3'd3: nxt10 = 3'd7;
      3'd4: nxt10 = 3'd5;
      3'd5: nxt10 = 3'd6;
      3'd6: nxt10 = 3'd4;
      3'd7: nxt10 = 3'd2;
      default: nxt10 = s;
    endcase
  endfunction

  function automatic logic [2:0] nxt01 (input logic [2:0] s);
    case (s)
      3'd0: nxt01 = 3'd2;
      3'd1: nxt01 = 3'd0;
      3'd2: nxt01 = 3'd6;
      3'd3: nxt01 = 3'd4;
      3'd4: nxt01 = 3'd2;
      3'd5: nxt01 = 3'd1;
      3'd6: nxt01 = 3'd3;
      3'd7: nxt01 = 3'd5;
      default: nxt01 = s;
    endcase
  endfunction

  // Input qualifiers at current sample
  wire in10_now =  in[0] & ~in[1];
  wire in01_now = ~in[0] &  in[1];
  wire else_now = ~(in10_now | in01_now);

  // 1) State encoding (upper bits must be 0 since case uses 3'bxxx)
  a_state_legal: assert property (@(posedge clk) state[7:3] == '0);

  // 2) Next-state function (one-cycle latency)
  a_ns_10: assert property (@(posedge clk)
    past_valid && $past(in10_now) |-> state[2:0] == nxt10($past(state[2:0]))
  );

  a_ns_01: assert property (@(posedge clk)
    past_valid && $past(in01_now) |-> state[2:0] == nxt01($past(state[2:0]))
  );

  a_ns_hold: assert property (@(posedge clk)
    past_valid && $past(else_now) |-> state[2:0] == $past(state[2:0])
  );

  // 3) Output function depends only on in[1:0] (one-cycle latency)
  a_out_func: assert property (@(posedge clk)
    past_valid |->
      out == ( $past(in10_now) ? 2'b10
            : $past(in01_now) ? 2'b01
            :                    2'b00 )
  );

  // 4) Output value set is constrained (redundant with a_out_func but explicit)
  a_out_set: assert property (@(posedge clk)
    out inside {2'b00,2'b01,2'b10}
  );

  // Coverage

  // Reach all 8 states
  genvar gi;
  generate
    for (gi=0; gi<8; gi++) begin: C_STATES
      cover property (@(posedge clk) state[2:0] == gi[2:0]);
    end
  endgenerate

  // Exercise all transitions from each state for in10, in01, and hold
  generate
    for (gi=0; gi<8; gi++) begin: C_TRANS
      localparam logic [2:0] S = gi[2:0];
      cover property (@(posedge clk) state[2:0]==S && in10_now |=> state[2:0]==nxt10(S) && out==2'b10);
      cover property (@(posedge clk) state[2:0]==S && in01_now |=> state[2:0]==nxt01(S) && out==2'b01);
      cover property (@(posedge clk) state[2:0]==S && else_now |=> state[2:0]==S && out==2'b00);
    end
  endgenerate

  // Cover all output values
  cover property (@(posedge clk) out==2'b10);
  cover property (@(posedge clk) out==2'b01);
  cover property (@(posedge clk) out==2'b00);

endmodule

// Bind into the DUT
bind FSM fsm_sva #(.n(n), .m(m)) fsm_sva_i(.*);