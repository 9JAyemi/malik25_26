// SVA checker for top_module
module top_module_sva (
  input logic       clk,
  input logic       reset,
  input logic       a,b,c,
  input logic [7:0] q
);
  logic [3:0] dec, cnt;
  assign dec = q[3:0];
  assign cnt = q[7:4];

  // Decoder: functional equivalence and sanity
  assert property (@(posedge clk) dec[3] == ~(a & b & c));
  assert property (@(posedge clk) dec[2] == ~(a & b & ~c));
  assert property (@(posedge clk) dec[1] == ~(a & ~b & c));
  assert property (@(posedge clk) dec[0] == ~(a & ~b & ~c));
  assert property (@(posedge clk) a==1 |-> $onehot(~dec));
  assert property (@(posedge clk) a==0 |-> dec==4'b1111);
  assert property (@(posedge clk) (!$isunknown({a,b,c})) |-> !$isunknown(dec));
  assert property (@(posedge clk) $stable({a,b,c}) |-> $stable(dec));

  // Counter: reset, increment, and no X/Z
  assert property (@(posedge clk) reset |-> cnt==4'h0);
  assert property (@(posedge clk) !$isunknown(cnt));
  assert property (@(posedge clk) disable iff (reset) cnt == $past(cnt) + 4'd1);

  // Optional bit-level increment invariants (strengthen debug)
  assert property (@(posedge clk) disable iff (reset) cnt[0] == ~$past(cnt[0]));
  assert property (@(posedge clk) disable iff (reset) cnt[1] == ($past(cnt[1]) ^ $past(cnt[0])));
  assert property (@(posedge clk) disable iff (reset) cnt[2] == ($past(cnt[2]) ^ ($past(cnt[1]) & $past(cnt[0]))));
  assert property (@(posedge clk) disable iff (reset) cnt[3] == ($past(cnt[3]) ^ ($past(cnt[2]) & $past(cnt[1]) & $past(cnt[0]))));

  // Coverage: full counter cycle including rollover
  cover property (@(posedge clk) disable iff (reset)
    cnt==4'h0 ##1 cnt==4'h1 ##1 cnt==4'h2 ##1 cnt==4'h3 ##1
    cnt==4'h4 ##1 cnt==4'h5 ##1 cnt==4'h6 ##1 cnt==4'h7 ##1
    cnt==4'h8 ##1 cnt==4'h9 ##1 cnt==4'hA ##1 cnt==4'hB ##1
    cnt==4'hC ##1 cnt==4'hD ##1 cnt==4'hE ##1 cnt==4'hF ##1 cnt==4'h0
  );

  // Coverage: all decoder cases
  cover property (@(posedge clk) a==0 && dec==4'b1111);
  cover property (@(posedge clk) a && b && c   && dec==4'b0111);
  cover property (@(posedge clk) a && b && !c  && dec==4'b1011);
  cover property (@(posedge clk) a && !b && c  && dec==4'b1101);
  cover property (@(posedge clk) a && !b && !c && dec==4'b1110);
endmodule

// Bind into DUT
bind top_module top_module_sva u_top_module_sva (
  .clk(clk), .reset(reset), .a(a), .b(b), .c(c), .q(q)
);