// SVA binders for the provided modules. Concise, high-signal-quality checks and coverage.

////////////////////////////////////////////////////////////
// Generic mux checker: o must equal i[s*W+:W] for all s
////////////////////////////////////////////////////////////
module mux_ref_sva #(parameter int N=1, W=1)
(
  input  logic [N*W-1:0]            i,
  input  logic [$clog2(N)-1:0]      s,
  input  logic [W-1:0]              o
);
  event comb_ev;
  always @* -> comb_ev;

  // Functional equivalence (includes X handling and out-of-range s)
  assert property (@(comb_ev) o === i[s*W +: W])
    else $error("%m: o != i[s] (s=%0d)", s);

  // Knownness: if selected slice is known and s is in range, o must be known
  assert property (@(comb_ev) (s < N && !$isunknown(i[s*W +: W])) |-> !$isunknown(o))
    else $error("%m: o has X/Z while selected input is known (s=%0d)", s);

  // Coverage: hit every valid select and at least one invalid
  genvar k;
  generate
    for (k=0; k<N; k++) begin : g_cov
      cover property (@(comb_ev) s==k && o === i[k*W +: W]);
    end
  endgenerate
  cover property (@(comb_ev) (s >= N));
  cover property (@(comb_ev) (s >= N) && $isunknown(o));
endmodule

bind mux_if_unbal_4_1              mux_ref_sva #(.N(N), .W(W)) M (.i(i), .s(s), .o(o));
bind mux_if_unbal_5_3              mux_ref_sva #(.N(N), .W(W)) M (.i(i), .s(s), .o(o));
bind mux_if_unbal_5_3_invert       mux_ref_sva #(.N(N), .W(W)) M (.i(i), .s(s), .o(o));
bind mux_if_unbal_5_3_width_mismatch mux_ref_sva #(.N(N), .W(W)) M (.i(i), .s(s), .o(o));
bind mux_if_unbal_4_1_missing      mux_ref_sva #(.N(N), .W(W)) M (.i(i), .s(s), .o(o));
bind mux_if_unbal_5_3_order        mux_ref_sva #(.N(N), .W(W)) M (.i(i), .s(s), .o(o));
bind mux_if_unbal_4_1_nonexcl      mux_ref_sva #(.N(N), .W(W)) M (.i(i), .s(s), .o(o));
bind mux_if_unbal_5_3_nonexcl      mux_ref_sva #(.N(N), .W(W)) M (.i(i), .s(s), .o(o));
bind mux_case_unbal_8_7            mux_ref_sva #(.N(N), .W(W)) M (.i(i), .s(s), .o(o));
bind mux_if_bal_8_2                mux_ref_sva #(.N(N), .W(W)) M (.i(i), .s(s), .o(o));
bind mux_if_bal_5_1                mux_ref_sva #(.N(N), .W(W)) M (.i(i), .s(s), .o(o));

////////////////////////////////////////////////////////////
// Priority mux: o = z?d : y?c : x?b : a
////////////////////////////////////////////////////////////
module prio4_sva
(
  input  logic x, y, z,
  input  logic a, b, c, d,
  input  logic o
);
  event comb_ev;
  always @* -> comb_ev;

  assert property (@(comb_ev) o === (z ? d : (y ? c : (x ? b : a))))
    else $error("%m: priority select mismatch");

  // Coverage: each priority level wins
  cover property (@(comb_ev) !x && !y && !z); // default a
  cover property (@(comb_ev)  x && !y && !z); // b
  cover property (@(comb_ev)      y && !z);   // c (regardless of x)
  cover property (@(comb_ev)           z);    // d
endmodule

bind cliffordwolf_nonexclusive_select prio4_sva P (.x(x), .y(y), .z(z), .a(a), .b(b), .c(c), .d(d), .o(o));

////////////////////////////////////////////////////////////
// freduce: sequential ifs -> final priority s==2 > s==1 > s==0 > default
////////////////////////////////////////////////////////////
module freduce_sva
(
  input  logic [1:0] s,
  input  logic a, b, c, d,
  input  logic [3:0] o
);
  event comb_ev;
  always @* -> comb_ev;

  // Explicit width matching
  assert property (@(comb_ev)
    o === ( (s==2) ? {3'b000, d} :
            (s==1) ? {2'b00,  {2{c}}} :
            (s==0) ? {1'b0,   {3{b}}} :
                      {4{a}} ) )
    else $error("%m: freduce mismatch");

  // Coverage: each s branch
  cover property (@(comb_ev) s==0);
  cover property (@(comb_ev) s==1);
  cover property (@(comb_ev) s==2);
  cover property (@(comb_ev) s==3); // default
endmodule

bind cliffordwolf_freduce freduce_sva F (.s(s), .a(a), .b(b), .c(c), .d(d), .o(o));

////////////////////////////////////////////////////////////
// case_nonexclusive_select mapping
////////////////////////////////////////////////////////////
module case_nonexclusive_select_sva
(
  input  logic [1:0] x, y,
  input  logic a, b, c, d, e,
  input  logic o
);
  event comb_ev;
  always @* -> comb_ev;

  assert property (@(comb_ev)
    o === ( (x==2'd0 || x==2'd2) ? b :
            (x==2'd1)           ? c :
            (y==2'd0)           ? d :
            (y==2'd1)           ? e : a ) )
    else $error("%m: case_nonexclusive_select mismatch");

  // Coverage
  cover property (@(comb_ev) x==2'd0);
  cover property (@(comb_ev) x==2'd1);
  cover property (@(comb_ev) x==2'd2);
  cover property (@(comb_ev) x==2'd3);
  cover property (@(comb_ev) x==2'd3 && y==2'd0);
  cover property (@(comb_ev) x==2'd3 && y==2'd1);
  cover property (@(comb_ev) x==2'd3 && !(y inside {2'd0,2'd1}));
endmodule

bind case_nonexclusive_select case_nonexclusive_select_sva C (.x(x), .y(y), .a(a), .b(b), .c(c), .d(d), .e(e), .o(o));

////////////////////////////////////////////////////////////
// case_nonoverlap / case_overlap / case_overlap2 final function mapping
////////////////////////////////////////////////////////////
module case_map_sva
(
  input  logic [2:0] x,
  input  logic a, b, c, d, e,
  input  logic o
);
  event comb_ev;
  always @* -> comb_ev;

  // Unified resolved behavior
  assert property (@(comb_ev)
    o === ( (x==3'd0 || x==3'd2) ? b :
            (x==3'd1)           ? c :
            (x==3'd3 || x==3'd4)? d :
            (x==3'd5)           ? e : 1'b0 ) )
    else $error("%m: case mapping mismatch");

  // Coverage
  cover property (@(comb_ev) x==3'd0);
  cover property (@(comb_ev) x==3'd1);
  cover property (@(comb_ev) x==3'd2);
  cover property (@(comb_ev) x==3'd3);
  cover property (@(comb_ev) x==3'd4);
  cover property (@(comb_ev) x==3'd5);
  cover property (@(comb_ev) x==3'd6);
  cover property (@(comb_ev) x==3'd7);
endmodule

bind case_nonoverlap case_map_sva CN (.x(x), .a(a), .b(b), .c(c), .d(d), .e(e), .o(o));
bind case_overlap   case_map_sva CO (.x(x), .a(a), .b(b), .c(c), .d(d), .e(e), .o(o));
bind case_overlap2  case_map_sva C2 (.x(x), .a(a), .b(b), .c(c), .d(d), .e(e), .o(o));