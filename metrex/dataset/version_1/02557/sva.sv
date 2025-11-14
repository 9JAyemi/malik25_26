// SVA checker for address_filter
module address_filter_sva(
  input  logic        clk,
  input  logic        reset,
  input  logic        go,
  input  logic [7:0]  data,
  input  logic [2:0]  af_state,
  input  logic        match,
  input  logic        done
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  a_reset_state: assert property (reset |=> af_state == 3'b000);

  // Legal state encoding (111 unreachable)
  a_legal_state: assert property (disable iff (reset)
                                  af_state inside {3'b000,3'b001,3'b010,3'b011,3'b100,3'b101,3'b110});

  // Go handling (synchronous load)
  a_go_zero: assert property (disable iff (reset)
                              go && (data[0] == 1'b0) |=> af_state == 3'b000);
  a_go_one:  assert property (disable iff (reset)
                              go && (data[0] == 1'b1) |=> af_state == 3'b001);

  // State transitions when go==0
  a_t_000: assert property (disable iff (reset) !go && af_state==3'b000 |=> af_state==3'b000);
  a_t_001: assert property (disable iff (reset) !go && af_state==3'b001 |=> af_state==3'b010);
  a_t_010: assert property (disable iff (reset) !go && af_state==3'b010 |=> af_state==3'b011);
  a_t_011: assert property (disable iff (reset) !go && af_state==3'b011 |=> af_state==3'b100);
  a_t_100: assert property (disable iff (reset) !go && af_state==3'b100 |=> af_state==3'b101);
  a_t_101: assert property (disable iff (reset) !go && af_state==3'b101 |=> af_state==3'b110);
  a_t_110: assert property (disable iff (reset) !go && af_state==3'b110 |=> af_state==3'b000);

  // Output mapping
  a_match_map: assert property (match == (af_state == 3'b110));
  a_done_map:  assert property (done  == ((af_state == 3'b110) || (af_state == 3'b000)));

  // Output relationships
  a_match_implies_done: assert property (match |-> done);
  a_done_states_only:   assert property (done |-> (af_state inside {3'b000,3'b110}));

  // Coverage
  c_reset_to_idle:     cover property (reset ##1 af_state==3'b000);
  c_immediate_clear:   cover property (go && (data[0]==1'b0) ##1 af_state==3'b000);
  // Full successful walk to match then back to idle with go held low during walk
  c_full_walk:         cover property (go && (data[0]==1'b1)
                                       ##1 !go[*5]
                                       ##1 (af_state==3'b110)
                                       ##1 (af_state==3'b000));

endmodule

// Bind into DUT (exposes internal af_state)
bind address_filter address_filter_sva u_address_filter_sva(
  .clk(clk),
  .reset(reset),
  .go(go),
  .data(data),
  .af_state(af_state),
  .match(match),
  .done(done)
);