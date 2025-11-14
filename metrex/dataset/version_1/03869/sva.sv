// SVA checker for FSM
// Bind this to the DUT: bind FSM FSM_SVA #(.n(n), .m(m), .s(s)) u_fsm_sva (.*);

module FSM_SVA #(parameter int n=4, m=2, s=8)
(
  input logic               clk,
  input logic               rst,
  input logic [n-1:0]       in,
  input logic [m-1:0]       out,
  input logic [s-1:0]       state
);

  // Basic param sanity
  initial begin
    assert (n==4 && m==2 && s>=3)
      else $error("FSM params expected n=4 m=2 s>=3, got n=%0d m=%0d s=%0d", n,m,s);
  end

  // Zero-extend 3-bit state codes to s bits
  function automatic logic [s-1:0] S(input logic [2:0] v);
    S = {{s-3{1'b0}}, v};
  endfunction

  localparam logic [s-1:0]
    ST_RESET = S(3'b000),
    ST_A     = S(3'b001),
    ST_B     = S(3'b010),
    ST_C     = S(3'b011),
    ST_D     = S(3'b100),
    ST_E     = S(3'b101),
    ST_F     = S(3'b110),
    ST_G     = S(3'b111);

  default clocking cb @(posedge clk); endclocking
  // Use disable iff(rst) for transition/output checks; add explicit reset checks below.
  default disable iff (rst);

  // Reset behavior (async reset must present as RESET on clock)
  assert property (@(posedge clk) rst |-> state == ST_RESET);
  assert property (@(posedge clk) $fell(rst) |-> state == ST_RESET);

  // State encoding validity
  assert property (@(posedge clk) state[s-1:3] == '0);
  assert property (@(posedge clk) state inside {ST_RESET,ST_A,ST_B,ST_C,ST_D,ST_E,ST_F,ST_G});

  // Output is a pure function of state
  assert property (state==ST_RESET |-> out==2'b00);
  assert property (state==ST_A     |-> out==2'b01);
  assert property (state==ST_B     |-> out==2'b10);
  assert property (state==ST_C     |-> out==2'b11);
  assert property (state==ST_D     |-> out==2'b01);
  assert property (state==ST_E     |-> out==2'b10);
  assert property (state==ST_F     |-> out==2'b11);
  assert property (state==ST_G     |-> out==2'b00);

  // Legal transitions
  assert property (state==ST_RESET && in==4'b0000 |=> state==ST_A);

  assert property (state==ST_A && in==4'b0001 |=> state==ST_B);
  assert property (state==ST_A && in==4'b0010 |=> state==ST_C);

  assert property (state==ST_B && in==4'b0011 |=> state==ST_D);
  assert property (state==ST_B && in==4'b0100 |=> state==ST_E);

  assert property (state==ST_C && in==4'b0101 |=> state==ST_E);
  assert property (state==ST_C && in==4'b0110 |=> state==ST_F);

  assert property (state==ST_D && in==4'b0111 |=> state==ST_G);
  assert property (state==ST_E && in==4'b1000 |=> state==ST_G);
  assert property (state==ST_F && in==4'b1001 |=> state==ST_G);

  assert property (state==ST_G && in==4'b1010 |=> state==ST_RESET);

  // Hold behavior when no transition condition matches
  assert property (state==ST_RESET && in!=4'b0000 |=> state==ST_RESET);

  assert property (state==ST_A && !(in==4'b0001 || in==4'b0010) |=> state==ST_A);
  assert property (state==ST_B && !(in==4'b0011 || in==4'b0100) |=> state==ST_B);
  assert property (state==ST_C && !(in==4'b0101 || in==4'b0110) |=> state==ST_C);

  assert property (state==ST_D && in!=4'b0111 |=> state==ST_D);
  assert property (state==ST_E && in!=4'b1000 |=> state==ST_E);
  assert property (state==ST_F && in!=4'b1001 |=> state==ST_F);
  assert property (state==ST_G && in!=4'b1010 |=> state==ST_G);

  // Coverage: each state and each transition
  cover property (@(posedge clk) !rst ##1 state==ST_RESET);
  cover property (state==ST_A);
  cover property (state==ST_B);
  cover property (state==ST_C);
  cover property (state==ST_D);
  cover property (state==ST_E);
  cover property (state==ST_F);
  cover property (state==ST_G);

  cover property (state==ST_RESET && in==4'b0000 |=> state==ST_A);
  cover property (state==ST_A     && in==4'b0001 |=> state==ST_B);
  cover property (state==ST_A     && in==4'b0010 |=> state==ST_C);
  cover property (state==ST_B     && in==4'b0011 |=> state==ST_D);
  cover property (state==ST_B     && in==4'b0100 |=> state==ST_E);
  cover property (state==ST_C     && in==4'b0101 |=> state==ST_E);
  cover property (state==ST_C     && in==4'b0110 |=> state==ST_F);
  cover property (state==ST_D     && in==4'b0111 |=> state==ST_G);
  cover property (state==ST_E     && in==4'b1000 |=> state==ST_G);
  cover property (state==ST_F     && in==4'b1001 |=> state==ST_G);
  cover property (state==ST_G     && in==4'b1010 |=> state==ST_RESET);

endmodule

// Suggested bind (place in a separate file included in sim):
// bind FSM FSM_SVA #(.n(n), .m(m), .s(s)) u_fsm_sva (.*);