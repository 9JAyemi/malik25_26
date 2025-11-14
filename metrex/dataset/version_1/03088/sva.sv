// SVA checker for FSM
module fsm_sva #(parameter int n=2, m=1, s=3)
(
  input logic              clk,
  input logic              rst,
  input logic [n-1:0]      in,
  input logic [m-1:0]      out,
  input logic [s-1:0]      state
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Basic sanity
  a_no_x:           assert property (!$isunknown({state,out,in}));
  a_state_legal:    assert property (state inside {0,1,2});

  // Synchronous reset behavior (checks the cycle after rst=1)
  a_sync_reset:     assert property (@(posedge clk) $past(rst) |-> state==0);

  // Output is a pure decode of state
  a_out_lsb:        assert property (out[0] == (state==1));
  if (m>1) begin : g_upper_zero
    a_out_upper0:   assert property (out[m-1:1] == '0);
  end

  // Next-state function
  // For in==2'b01, next state is 1 from any legal state
  a_in01_to_s1:     assert property ((state inside {0,1,2}) && (in==2'b01) |=> state==1);

  // For in==2'b00, next state depends on current state
  a_s0_in00:        assert property ((state==0) && (in==2'b00) |=> state==0);
  a_s1_in00:        assert property ((state==1) && (in==2'b00) |=> state==2);
  a_s2_in00:        assert property ((state==2) && (in==2'b00) |=> state==0);

  // For in==2'b10 or 2'b11 (in[1]==1), hold current state
  a_hold_others:    assert property ((state inside {0,1,2}) && in[1] |=> state==$past(state));

  // Coverage: reach all states and exercise all arcs (including hold)
  c_reach_s0:       cover property (state==0);
  c_reach_s1:       cover property (state==1);
  c_reach_s2:       cover property (state==2);

  c_s0_00_s0:       cover property ((state==0)&&(in==2'b00) |=> state==0);
  c_s0_01_s1:       cover property ((state==0)&&(in==2'b01) |=> state==1);
  c_s1_00_s2:       cover property ((state==1)&&(in==2'b00) |=> state==2);
  c_s1_01_s1:       cover property ((state==1)&&(in==2'b01) |=> state==1);
  c_s2_00_s0:       cover property ((state==2)&&(in==2'b00) |=> state==0);
  c_s2_01_s1:       cover property ((state==2)&&(in==2'b01) |=> state==1);
  c_hold_10_11:     cover property ((state inside {0,1,2}) && in[1] |=> state==$past(state));

  // Reset to known state coverage
  c_reset_to_s0:    cover property ($rose(rst) ##1 state==0);

endmodule

// Bind into the DUT
bind FSM fsm_sva #(.n(n), .m(m), .s(s)) u_fsm_sva (
  .clk(clk),
  .rst(rst),
  .in(in),
  .out(out),
  .state(state)
);