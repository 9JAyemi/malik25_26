// SVA checker for gray_code_state_machine
module gray_code_state_machine_sva #(parameter int n = 4)
(
  input  logic              clk,
  input  logic              rst,
  input  logic [n-1:0]      state,
  input  logic [n-1:0]      next_state
);

  localparam logic [n-1:0] MAX = {n{1'b1}};

  function automatic logic [n-1:0] f_gray(input logic [n-1:0] b);
    return b ^ (b >> 1);
  endfunction

  // Parameter sanity
  initial assert (n >= 1)
    else $error("n must be >= 1");

  // No X/Z on observed cycles
  assert property (@(posedge clk) !$isunknown(state) && !$isunknown(next_state));

  // Reset behavior: hold zeros while rst=1 on clock edges
  assert property (@(posedge clk) rst |-> (next_state == '0 && state == '0));

  // Output equals Gray(next_state)
  assert property (@(posedge clk) state == f_gray(next_state));

  // Binary counter steps by +1 modulo 2^n (skip check if previous cycle was in reset)
  assert property (@(posedge clk) disable iff (rst)
                   $past(!rst) |-> ((next_state == $past(next_state) + 1) ||
                                    ($past(next_state) == MAX && next_state == '0)));

  // If we observe next_state == 0 (and previous cycle not in reset), we must have wrapped from MAX
  assert property (@(posedge clk) disable iff (rst)
                   $past(!rst) && (next_state == '0) |-> ($past(next_state) == MAX));

  // Gray adjacency: exactly one bit toggles between consecutive states
  assert property (@(posedge clk) disable iff (rst)
                   $past(!rst) |-> $onehot(state ^ $past(state)));

  // Coverage: observe a wrap event (MAX -> 0) and at least one toggle on each bit
  cover property (@(posedge clk) disable iff (rst)
                  $past(next_state) == MAX && next_state == '0);

  genvar i;
  generate
    for (i = 0; i < n; i++) begin : C_BIT_TOGGLE
      cover property (@(posedge clk) disable iff (rst) $changed(state[i]));
    end
  endgenerate

endmodule

// Bind into the DUT (connect internal next_state)
bind gray_code_state_machine
  gray_code_state_machine_sva #(.n(n)) u_gray_code_state_machine_sva (
    .clk(clk),
    .rst(rst),
    .state(state),
    .next_state(next_state)
  );