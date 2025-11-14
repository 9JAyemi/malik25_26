// SVA for one_hot_state_machine
// Bind-friendly, checks one-hot encoding, reset behavior, transition function, and covers all states/transitions.

module one_hot_state_machine_sva #(parameter int n = 4)
(
  input logic               clk,
  input logic               rst,
  input logic [n-1:0]       in,
  input logic [n-1:0]       out
);

  // Ensure expected parameterization
  initial if (n != 4) $error("SVA expects n==4, got %0d", n);

  // Canonical one-hot encodings (sized to n)
  localparam logic [n-1:0] S0 = logic'((1 << 0));
  localparam logic [n-1:0] S1 = logic'((1 << 1));
  localparam logic [n-1:0] S2 = logic'((1 << 2));
  localparam logic [n-1:0] S3 = logic'((1 << 3));

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Helpers
  let is_zero = (in == '0);
  let s0 = (out == S0);
  let s1 = (out == S1);
  let s2 = (out == S2);
  let s3 = (out == S3);
  let known_in = !$isunknown(in);
  let known_out = !$isunknown(out);

  // Reset behavior (async and sync)
  assert property (@(posedge rst) out == S0)
    else $error("Async reset did not force STATE0");
  assert property (rst |-> out == S0)
    else $error("While reset asserted, out must be STATE0");

  // One-hot and legality
  assert property (known_out && $onehot(out))
    else $error("out must be one-hot and known");

  // Functional next-state mapping (only when input is known)
  assert property ((s0 && known_in) |=> (is_zero ? s0 : s1))
    else $error("STATE0 transition violated");
  assert property ((s1 && known_in) |=> (is_zero ? s2 : s3))
    else $error("STATE1 transition violated");
  assert property ((s2 && known_in) |=> (is_zero ? s0 : s1))
    else $error("STATE2 transition violated");
  assert property ((s3 && known_in) |=> (is_zero ? s2 : s3))
    else $error("STATE3 transition violated");

  // Even if input goes unknown, next state must remain one-hot and within legal set
  assert property ((s0 or s1 or s2 or s3) |=> $onehot(out))
    else $error("Next out is not one-hot");

  // Coverage: reachability of all states
  cover property (s0);
  cover property (s1);
  cover property (s2);
  cover property (s3);

  // Coverage: all eight transitions under both input classes
  cover property (s0 && is_zero |=> s0);
  cover property (s0 && !is_zero |=> s1);
  cover property (s1 && is_zero |=> s2);
  cover property (s1 && !is_zero |=> s3);
  cover property (s2 && is_zero |=> s0);
  cover property (s2 && !is_zero |=> s1);
  cover property (s3 && is_zero |=> s2);
  cover property (s3 && !is_zero |=> s3);

endmodule

// Bind into DUT
bind one_hot_state_machine one_hot_state_machine_sva #(.n(n))
  one_hot_state_machine_sva_i (.clk(clk), .rst(rst), .in(in), .out(out));