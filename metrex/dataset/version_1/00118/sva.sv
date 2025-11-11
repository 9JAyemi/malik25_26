// SVA for wallace multiplier and its sub-blocks (concise, high-quality checks)
// Bind this file to your compiled DUT

// ---------------- Sub-block checkers ----------------
module ha_sva(input logic a,b, c,s);
  default clocking cb @(*); endclocking
  // HA must compute 2-bit sum of a+b
  assert property ({c,s} == a + b);
  // Known-prop
  assert property (!$isunknown({a,b}) |-> ##0 !$isunknown({c,s}));
endmodule

module fa_sva(input logic a,b,c, cy,sm);
  default clocking cb @(*); endclocking
  // FA must compute 2-bit sum of a+b+c
  assert property ({cy,sm} == a + b + c);
  assert property (!$isunknown({a,b,c}) |-> ##0 !$isunknown({cy,sm}));
endmodule

module fad_sva(input logic a,b,c, cy,sm);
  default clocking cb @(*); endclocking
  // FAd must also compute a+b+c
  assert property ({cy,sm} == a + b + c);
  assert property (!$isunknown({a,b,c}) |-> ##0 !$isunknown({cy,sm}));
endmodule

module mux_sva(input logic i0,i1,s, o);
  default clocking cb @(*); endclocking
  assert property (o == (s ? i1 : i0));
  assert property (!$isunknown({i0,i1,s}) |-> ##0 !$isunknown(o));
endmodule

bind HA   ha_sva   ha_sva_i(.a(a),.b(b),.c(c),.s(s));
bind FA   fa_sva   fa_sva_i(.a(a),.b(b),.c(c),.cy(cy),.sm(sm));
bind FAd  fad_sva  fad_sva_i(.a(a),.b(b),.c(c),.cy(cy),.sm(sm));
bind MUX  mux_sva  mux_sva_i(.i0(i0),.i1(i1),.s(s),.o(o));

// ---------------- Top-level wallace checker ----------------
module wallace_sva(
  input  logic [7:0]  x,y,
  input  logic [15:0] p,
  // internal partial products/flags
  input  logic [6:0]  ip1,
  input  logic [7:0]  ip2,ip3,ip4,ip5,ip6,ip7,ip8,si,iip,
  input  logic        c
);
  default clocking cb @(*); endclocking

  // No-X propagation on known inputs
  assert property (!$isunknown({x,y}) |-> ##0 !$isunknown({p,ip1,ip2,ip3,ip4,ip5,ip6,ip7,ip8,si,iip,c}));

  // Golden functional check: 8x8 -> 16 multiply
  assert property (p == x * y);

  // Basic LSB check
  assert property (p[0] == (x[0] & y[0]));

  // Partial product checks
  genvar k;
  // ip1: y[0] with x[1..7]
  for (k=0; k<7; k++) begin : G_IP1
    assert property (ip1[k] == (x[k+1] & y[0]));
  end
  // ip2..ip7: straight AND planes
  for (k=0; k<8; k++) begin : G_IP2_7
    assert property (ip2[k] == (x[k] & y[1]));
    assert property (ip3[k] == (x[k] & y[2]));
    assert property (ip4[k] == (x[k] & y[3]));
    assert property (ip5[k] == (x[k] & y[4]));
    assert property (ip6[k] == (x[k] & y[5]));
    assert property (ip7[k] == (x[k] & y[6]));
    // iip: AND plane for y[7]
    assert property (iip[k] == (x[k] & y[7]));
    // ip8 per DUT definition
    assert property (ip8[k] == (y[7] ^ iip[k])); // equivalent to y[7] & ~x[k]
  end

  // si flags: MSB negations per row
  assert property (si[0] == ~ip1[6]);
  assert property (si[1] == ~ip2[7]);
  assert property (si[2] == ~ip3[7]);
  assert property (si[3] == ~ip4[7]);
  assert property (si[4] == ~ip5[7]);
  assert property (si[5] == ~ip6[7]);
  assert property (si[6] == ~ip7[7]);
  assert property (si[7] == ~ip8[7]);

  // Final HA with 1'b1 implies c == ~p[15] (since s = a^1 and c = a&1)
  // This ties out the final carry behavior exported as wire c
  assert property (c == ~p[15]);

  // Minimal but meaningful covers
  cover property (x == 8'h00 || y == 8'h00);          // zero multiplicand
  cover property (x == 8'hFF && y == 8'hFF);          // max*max => 16'hFE01
  cover property (x == 8'h01 && y == 8'h80);          // MSB of y only
  cover property (x == 8'hAA && y == 8'h55);          // pattern mix
  cover property (p[15]);                              // high product bit set
endmodule

bind wallace wallace_sva wsva(
  .x(x), .y(y), .p(p),
  .ip1(ip1), .ip2(ip2), .ip3(ip3), .ip4(ip4), .ip5(ip5), .ip6(ip6), .ip7(ip7), .ip8(ip8),
  .si(si), .iip(iip), .c(c)
);