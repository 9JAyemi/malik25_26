// SVA for johnson_counter
// Bind these checks to the DUT (accesses internal 'state')
bind johnson_counter johnson_counter_sva #(.n(n)) u_johnson_counter_sva();

module johnson_counter_sva #(parameter int n = 4) ();
  // Access bound-instance signals directly: clk, out1, out2, state
  default clocking @(posedge clk); endclocking

  // Start checking once the state becomes fully known at least once
  logic started;
  always_ff @(posedge clk) started <= started || !$isunknown(state);

  // Output mapping and complement, no X/Z once started
  a_out_map:     assert property (started |-> (out1 == state[0] && out2 == ~state[0]));
  a_out_compl:   assert property (started |-> (out1 === ~out2));
  a_out_known:   assert property (started |-> !$isunknown({out1,out2}));

  // State transition rule: shift + inverted MSB insertion
  genvar i;
  generate
    for (i = 1; i < n; i++) begin : GEN_SHIFT
      a_shift: assert property (started |-> state[i] == $past(state[i-1]));
    end
  endgenerate
  a_lsb_insert: assert property (started |-> state[0] == ~ $past(state[n-1]));

  // Once known, state remains known
  a_known_preserve: assert property ($past(started) |-> !$isunknown(state));

  // Johnson-set closure: once in a Johnson state, always stays in the set
  function automatic bit is_johnson(input logic [n-1:0] v);
    int cnt = 0;
    for (int j = 0; j < n-1; j++) cnt += (v[j] ^ v[j+1]);
    return (cnt <= 1); // at most one 0/1 transition => single run of 1s or 0s
  endfunction
  a_closure: assert property (started && is_johnson($past(state)) |-> is_johnson(state));

  // Period and extremal-state assertions when hitting all-zero
  localparam logic [n-1:0] ALL_ONES = {n{1'b1}};
  a_reach_all_ones: assert property (started && state == '0 |-> ##[1:n] state == ALL_ONES);
  a_full_period:    assert property (started && state == '0 |-> (state != '0)[* (2*n-1)] ##1 state == '0);

  // Coverage: hit every Johnson state (low-run and its complement)
  function automatic logic [n-1:0] ones_run(input int k);
    logic [n-1:0] r = '0;
    for (int j = 0; j < k && j < n; j++) r[j] = 1'b1;
    return r;
  endfunction
  genvar k;
  generate
    for (k = 0; k <= n; k++) begin : COV_STATES
      c_low_run: cover property (started && state == ones_run(k));
      c_high_run: cover property (started && state == (ALL_ONES ^ ones_run(k)));
    end
  endgenerate

  // Coverage: observe full 2n cycle from zero, and reaching all-ones
  c_cycle:     cover property (started && state == '0 ##1 (state != '0)[* (2*n-1)] ##1 state == '0);
  c_all_ones:  cover property (started && state == '0 ##[1:n] state == ALL_ONES);
endmodule