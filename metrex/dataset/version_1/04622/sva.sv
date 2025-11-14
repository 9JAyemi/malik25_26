// SVA for adder and its muxes. Bind into DUTs as shown at bottom.

module adder_sva #(parameter W=4)
(
  input  logic [W-1:0] a,
  input  logic [W-1:0] b,
  input  logic         cin,
  input  logic [W-1:0] sum,
  input  logic         cout
);
  // Functional golden check (allow a delta for combinational settle)
  property p_add_ok;
    @(a or b or cin) ##0 {cout,sum} == (a + b + cin);
  endproperty
  assert property (p_add_ok);

  // Bitwise ripple-carry structure check
  let p  = a ^ b;
  let g  = a & b;
  let c1 = g[0] | (p[0] & cin);
  let c2 = g[1] | (p[1] & c1);
  let c3 = g[2] | (p[2] & c2);
  let c4 = g[3] | (p[3] & c3);

  property p_bitwise_ok;
    @(a or b or cin) ##0
      (sum[0] == (p[0]^cin)) &&
      (sum[1] == (p[1]^c1 )) &&
      (sum[2] == (p[2]^c2 )) &&
      (sum[3] == (p[3]^c3 )) &&
      (cout    ==  c4       );
  endproperty
  assert property (p_bitwise_ok);

  // X-propagation guard
  property p_no_x_out;
    @(a or b or cin) (!$isunknown({a,b,cin})) |-> ##0 !$isunknown({sum,cout});
  endproperty
  assert property (p_no_x_out);

  // Concise functional coverage
  cover property (@(a or b or cin) ##0 ({cout,sum} == 5'd0));     // min
  cover property (@(a or b or cin) ##0 ({cout,sum} == 5'd31));    // max
  cover property (@(a or b or cin) (a==4'hF && b==4'h0 && !cin) ##0 (!cout && sum==4'hF));
  cover property (@(a or b or cin) (a==4'h0 && b==4'h0 && !cin) ##0 (!cout && sum==4'h0));
  // pure propagate chain: p=4'hF, g=0, cin=1 -> cout=1, sum=0
  cover property (@(a or b or cin) ((a^b)==4'hF && (a&b)==4'h0 && cin) ##0 (sum==4'h0 && cout));
  // top-bit generate to carry-out, no propagate
  cover property (@(a or b or cin) (a[3] && b[3] && a[2:0]==3'b000 && b[2:0]==3'b000 && !cin) ##0 (cout && sum==4'h0));
endmodule


module mux2to1_sva #(parameter WIDTH=8)
(
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  input  logic             s,
  input  logic [WIDTH-1:0] y
);
  // Functional checks with delta settle
  property p_sel0; @(a or b or s) (!s && !$isunknown({a,s})) |-> ##0 (y==a); endproperty
  property p_sel1; @(a or b or s) ( s && !$isunknown({b,s})) |-> ##0 (y==b); endproperty
  assert property (p_sel0);
  assert property (p_sel1);

  // X-guard
  property p_mux_no_x; @(a or b or s) (!$isunknown({a,b,s})) |-> ##0 !$isunknown(y); endproperty
  assert property (p_mux_no_x);

  // Coverage of both select paths
  cover property (@(a or b or s) !s ##0 (y==a));
  cover property (@(a or b or s)  s ##0 (y==b));
endmodule


// Bind SVA into DUTs
bind adder   adder_sva   #(.W(4)) u_adder_sva   (.a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));
bind mux2to1 mux2to1_sva #(.WIDTH(WIDTH)) u_mux2to1_sva (.a(a), .b(b), .s(s), .y(y));