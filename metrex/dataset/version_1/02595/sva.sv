// SVA for gray_code_state_machine
// Concise, high-signal-importance checks + useful coverage

module gray_code_state_machine_sva #(parameter int N = 3)
(
  input logic              clk,
  input logic [N-1:0]      state,
  input logic [N-1:0]      next_state
);

  // Expected next state (column [1] of the DUT's transition table) for N=3
  function automatic logic [N-1:0] expected_next(input logic [N-1:0] s);
    unique case (s)
      3'h0: expected_next = 3'h2;
      3'h1: expected_next = 3'h0;
      3'h2: expected_next = 3'h7;
      3'h3: expected_next = 3'h4;
      3'h4: expected_next = 3'h5;
      3'h5: expected_next = 3'h6;
      3'h6: expected_next = 3'h1;
      3'h7: expected_next = 3'h3;
      default: expected_next = 'x;
    endcase
  endfunction

  // Functional: next_state must equal the transition function of state (registered at posedge)
  property p_next_matches;
    @(posedge clk) !$isunknown(state) |-> ##0 (next_state == expected_next(state));
  endproperty
  assert property (p_next_matches);

  // Gray-code property: exactly one bit toggles between state and next_state
  property p_gray_1bit_toggle;
    @(posedge clk) !$isunknown(state) |-> ##0 $onehot(state ^ next_state);
  endproperty
  assert property (p_gray_1bit_toggle);

  // Cleanliness: known state yields known next_state
  property p_no_x_propagation;
    @(posedge clk) !$isunknown(state) |-> ##0 !$isunknown(next_state);
  endproperty
  assert property (p_no_x_propagation);

  // Registered-only output: no glitches between rising edges
  assert property (@(negedge clk) $stable(next_state));

  // Coverage: see all states and their intended transitions; also each bit flips at least once
  genvar i;
  generate
    for (i = 0; i < (1<<N); i++) begin : COV_STATES
      cover property (@(posedge clk) (state == i) ##0 (next_state == expected_next(i[N-1:0])));
    end
  endgenerate

  genvar b;
  generate
    for (b = 0; b < N; b++) begin : COV_BITFLIP
      cover property (@(posedge clk) ##0 ((state ^ next_state) == ({{(N-1){1'b0}},1'b1} << b)));
    end
  endgenerate

  // Overall Gray transition observed at least once
  cover property (@(posedge clk) ##0 $onehot(state ^ next_state));

endmodule

bind gray_code_state_machine
  gray_code_state_machine_sva #(.N(n))
  u_gray_code_state_machine_sva (.clk(clk), .state(state), .next_state(next_state));