// SVA for johnson_counter
// Focused, concise checks and coverage; bind into DUT scope

module johnson_counter_sva #(parameter int n = 4)
(
  input logic                   clk,
  input logic [n-1:0]           out,
  input logic [n-1:0]           state,
  input logic [n-1:0]           next_state
);

  // The RTL hard-codes next_state[0..3]; prevent misuse
  initial assert (n == 4)
    else $error("johnson_counter expects n==4; got n=%0d", n);

  // Helpers
  function automatic logic [n-1:0] rotl1 (input logic [n-1:0] v);
    rotl1 = {v[n-2:0], v[n-1]}; // v rotated left by 1 (LSB gets former MSB)
  endfunction

  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown({state,next_state,out}));

  bit started;
  always @(posedge clk) started <= 1'b1;

  // Combinational correctness of next_state function
  assert property (next_state == (state ^ rotl1(state)));

  // Sequential update: state <= next_state
  assert property (started |-> state == $past(next_state));

  // Equivalent one-line state recurrence
  assert property (started |-> state == ($past(state) ^ rotl1($past(state))));

  // out mirrors state
  assert property (out == state);

  // Parity properties: XOR-reduction of next_state is always 0; state parity 0 from 2nd cycle
  assert property ((^next_state) == 1'b0);
  assert property (started |-> (^state) == 1'b0);

  // Bitwise sequential relation and toggle coverage
  genvar i;
  generate
    for (i = 0; i < n; i++) begin : g_bit
      localparam int L = (i==0) ? (n-1) : (i-1);
      assert property (started |-> state[i] == ($past(state[L]) ^ $past(state[i])));
      cover  property ($rose(state[i]));
      cover  property ($fell(state[i]));
    end
  endgenerate

  // State-level coverage
  cover property ($changed(state));
  cover property (state != '0);
  cover property (state == '0);

endmodule

bind johnson_counter johnson_counter_sva #(.n(n)) u_johnson_counter_sva (.*);