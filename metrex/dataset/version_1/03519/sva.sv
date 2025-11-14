// SVA for multiplier_block (place inside module or bind)

`ifndef SYNTHESIS
// No-X propagation when input is known
assert property (@(*) !$isunknown(i_data0) |-> !$isunknown({w1,w256,w257,w4,w32,w261,w229,w29312,o_data0}));

// Stage-by-stage functional checks
assert property (@(*) w1      == i_data0);
assert property (@(*) w256    == (i_data0 << 8));
assert property (@(*) w257    == (w1 + w256));
assert property (@(*) w4      == (i_data0 << 2));
assert property (@(*) w32     == (i_data0 << 5));
assert property (@(*) w261    == (w257 + w4));
assert property (@(*) w229    == (w261 - w32));
assert property (@(*) w29312  == (w229 << 7));
assert property (@(*) o_data0 == w29312);

// Collapsed algebraic equivalence checks
assert property (@(*) w257    == ($unsigned(i_data0) * 32'd257)[31:0]);
assert property (@(*) w261    == ($unsigned(i_data0) * 32'd261)[31:0]);
assert property (@(*) w229    == ($unsigned(i_data0) * 32'd229)[31:0]);
assert property (@(*) o_data0 == ($unsigned(i_data0) * 32'd29312)[31:0]);

// Coverage: key corner cases and overflow scenarios
cover  property (@(*) i_data0 == 32'h0000_0000);
cover  property (@(*) i_data0 == 32'hFFFF_FFFF);
cover  property (@(*) $onehot(i_data0));
cover  property (@(*) |i_data0[31:24]); // <<8 overflow potential
cover  property (@(*) |i_data0[31:27]); // <<5 overflow potential
cover  property (@(*) |i_data0[31:30]); // <<2 overflow potential
cover  property (@(*) ($unsigned(w257) < $unsigned(w1)));   // w1 + w256 overflow
cover  property (@(*) ($unsigned(w261) < $unsigned(w257))); // w257 + w4 overflow
cover  property (@(*) ((i_data0[24:0] == 25'h0) && (i_data0 != 0) && (o_data0 == 0))); // zero due to *2^7
`endif