// SVA for add2_and_round (combinational end-around-carry adder)
module add2_and_round_sva #(parameter WIDTH=16)
(
  input logic [WIDTH-1:0] in1,
  input logic [WIDTH-1:0] in2,
  input logic [WIDTH-1:0] sum
);
  function automatic logic [WIDTH-1:0] eac_sum(input logic [WIDTH-1:0] a,b);
    logic [WIDTH:0] t; t = a + b;
    return t[WIDTH-1:0] + t[WIDTH];
  endfunction

  logic [WIDTH:0] t_comb;
  assign t_comb = in1 + in2;

  // Functional correctness and X-prop
  always_comb begin
    assert (sum == eac_sum(in1,in2)) else $error("EAC sum mismatch");
    if (!$isunknown({in1,in2})) assert (!$isunknown(sum)) else $error("X on sum with known inputs");
    if (!t_comb[WIDTH]) assert (sum == t_comb[WIDTH-1:0]) else $error("No-carry case wrong");
    if ( t_comb[WIDTH]) assert (sum == t_comb[WIDTH-1:0] + 1'b1) else $error("Carry case wrong");
    if (sum == '0) assert (in1=='0 && in2=='0) else $error("Zero result only when both inputs zero");
  end

  // Key corner coverage
  always_comb begin
    cover (!t_comb[WIDTH]);                      // no carry
    cover ( t_comb[WIDTH]);                      // carry
    cover (in1=='0 && in2=='0 && sum=='0);       // all zero
    cover (in1=={WIDTH{1'b1}} && in2=={{WIDTH-1{1'b0}},1'b1}); // max + 1
    cover (in1=={WIDTH{1'b1}} && in2=={WIDTH{1'b1}});          // max + max
  end
endmodule

// SVA for add2_and_round_reg (registered version, 1-cycle latency)
module add2_and_round_reg_sva #(parameter WIDTH=16)
(
  input logic                   clk,
  input logic [WIDTH-1:0]       in1,
  input logic [WIDTH-1:0]       in2,
  input logic [WIDTH-1:0]       sum
);
  function automatic logic [WIDTH-1:0] eac_sum(input logic [WIDTH-1:0] a,b);
    logic [WIDTH:0] t; t = a + b;
    return t[WIDTH-1:0] + t[WIDTH];
  endfunction

  logic past_v;
  initial past_v = 1'b0;
  always_ff @(posedge clk) past_v <= 1'b1;

  // Functional correctness (1-cycle latency)
  assert property (@(posedge clk) past_v |-> sum == eac_sum($past(in1), $past(in2)))
    else $error("Registered EAC sum mismatch");

  // X-prop
  assert property (@(posedge clk) past_v && !$isunknown({$past(in1),$past(in2)}) |-> !$isunknown(sum))
    else $error("X on sum with known past inputs");

  // Conditional correctness wrt carry
  assert property (@(posedge clk)
    past_v && (($past(in1)+$past(in2))[WIDTH]==1'b0)
    |-> sum == ($past(in1)+$past(in2))[WIDTH-1:0])
    else $error("No-carry registered case wrong");

  assert property (@(posedge clk)
    past_v && (($past(in1)+$past(in2))[WIDTH]==1'b1)
    |-> sum == (($past(in1)+$past(in2))[WIDTH-1:0] + 1'b1))
    else $error("Carry registered case wrong");

  // Zero result only when past inputs were zero
  assert property (@(posedge clk) past_v && sum=='0 |-> ($past(in1)=='0 && $past(in2)=='0))
    else $error("Zero result without zero past inputs");

  // Coverage
  cover property (@(posedge clk) past_v && (($past(in1)+$past(in2))[WIDTH]==0));
  cover property (@(posedge clk) past_v && (($past(in1)+$past(in2))[WIDTH]==1));
  cover property (@(posedge clk) past_v && $past(in1)=='0 && $past(in2)=='0 && sum=='0);
  cover property (@(posedge clk) past_v && $past(in1)=={WIDTH{1'b1}} && $past(in2)=={{WIDTH-1{1'b0}},1'b1});
  cover property (@(posedge clk) past_v && $past(in1)=={WIDTH{1'b1}} && $past(in2)=={WIDTH{1'b1}});
endmodule

// Bind directives
bind add2_and_round     add2_and_round_sva     #(.WIDTH(WIDTH)) i_add2_and_round_sva     (.*);
bind add2_and_round_reg add2_and_round_reg_sva #(.WIDTH(WIDTH)) i_add2_and_round_reg_sva (.*);