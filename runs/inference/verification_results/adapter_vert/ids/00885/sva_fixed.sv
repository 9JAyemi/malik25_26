module chacha_qr_sva (
    input logic a,
    input logic a0,
    input logic a1,
    input logic b,
    input logic b0,
    input logic b1,
    input logic b2,
    input logic b3,
    input logic c,
    input logic c0,
    input logic c1,
    input logic d,
    input logic d0,
    input logic d1,
    input logic d2,
    input logic d3,
    input logic clk_in_15
);

property ClockSynceotid; @(posedge clk_in_15) (a) == (a + b) && (d) == (d ^ a0) && (d1) == ({d0[15 : 0], d0[31 : 16]}) && (c) == (c + d1) && (b) == (b ^ c0) && (b1) == ({b0[19 : 0], b0[31 : 20]}) && (a1) == (a0 + b1) && (d2) == (d1 ^ a1) && (d3) == ({d2[23 : 0], d2[31 : 24]}) && (c1) == (c0 + d3) && (b2) == (b1 ^ c1) && (b3) == ({b2[24 : 0], b2[31 : 25]}); endproperty
assert property (ClockSynceotid);

endmodule