// SVA for sync_counter
module sync_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  out,
  input logic [3:0]  state
);
  // Ensure $past is safe
  logic started;
  initial started = 1'b0;
  always_ff @(posedge clk) started <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Basic safety
  a_knowns:       assert property (started |-> !$isunknown({state,out}));
  a_state_range:  assert property (started |-> state inside {[4'd0:4'd8]});
  a_out_range:    assert property (started |-> out   inside {[4'd0:4'd8]});

  // Synchronous reset behavior
  a_reset_clears: assert property (reset |=> (state==4'd0 && out==4'd0));

  // Functional relationships
  // Output reflects previous state
  a_out_prev_state: assert property (started |-> out == $past(state));

  // State progression: 0->1->...->8->0 when prior cycle not in reset
  a_state_next: assert property (started && !$past(reset)
                                 |-> state == (($past(state)==4'd8) ? 4'd0 : ($past(state)+4'd1)));

  // Coverage
  c_reset_seen:   cover property (reset ##1 !reset);
  c_wrap:         cover property (disable iff (reset) (state==4'd8) ##1 (state==4'd0));
  c_full_cycle:   cover property (disable iff (reset)
                      (state==4'd0) ##1 (state==4'd1) ##1 (state==4'd2) ##1 (state==4'd3) ##
                      (state==4'd4) ##1 (state==4'd5) ##1 (state==4'd6) ##1 (state==4'd7) ##
                      (state==4'd8) ##1 (state==4'd0));
endmodule

// Bind the SVA to the DUT (uses DUT's internal 'state')
bind sync_counter sync_counter_sva sva_i (.*);