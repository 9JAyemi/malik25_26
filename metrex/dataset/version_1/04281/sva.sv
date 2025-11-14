// Add these SVA inside module FP16BAddSubS4Of5 (after the assigns). Guarded for sim/formal only.

`ifndef SYNTHESIS
default clocking cb @(posedge clk); endclocking
default disable iff (rst)

// Sign bit
assert property (s == ((xn == yn) ? xs : (yn ? (neg ^ xs) : (neg ^ ys))));

// Normalization shifts
assert property (r8 == ((r[14:7]   == 8'h00) ? {r[6:0], 8'h00} : r));
assert property (r4 == ((r8[14:11] == 4'h0)  ? {r8[10:0], 4'h0} : r8));
assert property (r2 == ((r4[14:13] == 2'h0)  ? {r4[12:0], 2'h0} : r4));
assert property (r1 == ((r2[14]    == 1'b0)  ? {r2[13:0], 1'b0} : r2));

// l0count encoding (8,4,2,1)
assert property (l0count == { (r[14:7]   == 8'h00),
                              (r8[14:11] == 4'h0),
                              (r4[14:13] == 2'h0),
                              (r2[14]    == 1'b0) });

// rr select (note truncation on r1 arm)
assert property (rr == ((xn == yn) ? r[14:7] : r1[7:0]));

// Exponent adjust and underflow
assert property (e_l0adjust == ({1'b0, e} - {5'b0, l0count}));
assert property (underflow  == e_l0adjust[8]);
assert property (underflow  == (e < l0count));
assert property (e_adjust   == (underflow ? 8'h00 : e_l0adjust[7:0]));
assert property (e_final    == ((xn == yn) ? e : e_adjust));

// Mantissa final
assert property (r_final == (underflow ? 7'h00 : rr[6:0]));

// Output packing
assert property (ret_0 == {s, e_final, r_final});

// Functional coverage (hit all key branches)
cover property (xn == yn);
cover property (xn != yn &&  yn);
cover property (xn != yn && !yn);

cover property (r[14:7]   == 8'h00);
cover property (r8[14:11] == 4'h0);
cover property (r4[14:13] == 2'h0);
cover property (r2[14]    == 1'b0);

cover property (underflow);
cover property (!underflow);
`endif