
module d_ff_async_reset_set (
  input CLK,
  input D,
  input Reset,
  input Set,
  output reg Q
);

  wire next_q, q_next_r, q_next_s;

  assign q_next_s = Set;
  assign q_next_r = Reset;
  assign next_q = (q_next_s | (~q_next_r & ~q_next_s & D)) ^ Q;

  always @(posedge CLK)
    Q <= next_q;

endmodule