// Drop this SVA block into cf_mul (e.g., under `ifdef ASSERT_ON) or bind it.
// It checks pipeline alignment, arithmetic, and provides compact functional coverage.

`ifdef ASSERT_ON
// Default clocking
default clocking cb @(posedge clk); endclocking

// Warm-up to avoid $past depth hazards (3-cycle pipeline)
logic [2:0] warm;
always_ff @(posedge clk) warm <= {warm[1:0],1'b1};
wire ready1 = warm[0];
wire ready2 = warm[1];
wire ready3 = warm[2];

// Helpers to model p1 selection
function automatic [23:0] sel_2b(input [1:0] c, input [23:0] a1p, input [23:0] a1n, input [23:0] a2n);
  case (c)
    2'b11: sel_2b = a1n;
    2'b10: sel_2b = a2n;
    2'b01: sel_2b = a1p;
    default: sel_2b = 24'd0;
  endcase
endfunction

function automatic [23:0] sel_3b_shift(input [2:0] c, input [23:0] a1p, input [23:0] a1n,
                                       input [23:0] a2p, input [23:0] a2n, input int sh);
  automatic [23:0] base;
  case (c)
    3'b011: base = a2p;
    3'b100: base = a2n;
    3'b001, 3'b010: base = a1p;
    3'b101, 3'b110: base = a1n;
    default: base = 24'd0;
  endcase
  sel_3b_shift = base << sh;
endfunction

function automatic [23:0] sel_1b_shift(input bit b, input [23:0] a1p, input int sh);
  sel_1b_shift = b ? (a1p << sh) : 24'd0;
endfunction

// End-to-end functional check (unsigned magnitude times, sign passthrough; 3-cycle latency)
assert property (ready3 |-> data_p[23:0] == $past($unsigned(data_a[15:0]) * $unsigned(data_b), 3));
assert property (ready3 |-> data_p[24]   == $past(data_a[16], 3));

// Output composed from previous p3 stage (due to NBA semantics)
assert property (ready1 |-> data_p == $past({p3_sign, p3_data_p_0}));

// ddata pipeline alignment (3-cycle latency from ddata_in to ddata_out)
assert property (ready3 |-> ddata_out == $past(ddata_in, 3));

// Sign and ddata stage-by-stage propagation
assert property (ready1 |-> p1_sign  == $past(data_a[16]));
assert property (ready2 |-> p2_sign  == $past(p1_sign));
assert property (ready1 |-> p1_ddata == $past(ddata_in));
assert property (ready2 |-> p2_ddata == $past(p1_ddata));
assert property (ready1 |-> p3_sign  == $past(p2_sign));
assert property (ready1 |-> p3_ddata == $past(p2_ddata));
assert property (ready1 |-> data_p[24] == $past(p3_sign));
assert property (ready1 |-> ddata_out  == $past(p3_ddata));

// p1 partial-product selection checks (registered 1 cycle after selection)
// Use $past() on p1_data_a_* wires and data_b slices.
assert property (ready1 |-> p1_data_p_0 == $past(sel_2b(data_b[1:0],  p1_data_a_1p_s, p1_data_a_1n_s, p1_data_a_2n_s)));
assert property (ready1 |-> p1_data_p_1 == $past(sel_3b_shift(data_b[3:1], p1_data_a_1p_s, p1_data_a_1n_s, p1_data_a_2p_s, p1_data_a_2n_s, 2)));
assert property (ready1 |-> p1_data_p_2 == $past(sel_3b_shift(data_b[5:3], p1_data_a_1p_s, p1_data_a_1n_s, p1_data_a_2p_s, p1_data_a_2n_s, 4)));
assert property (ready1 |-> p1_data_p_3 == $past(sel_3b_shift(data_b[7:5], p1_data_a_1p_s, p1_data_a_1n_s, p1_data_a_2p_s, p1_data_a_2n_s, 6)));
assert property (ready1 |-> p1_data_p_4 == $past(sel_1b_shift(data_b[7],  p1_data_a_1p_s, 8)));

// p2 accumulation from p1 partials
assert property (ready2 |-> p2_data_p_0 == $past(p1_data_p_0 + p1_data_p_1 + p1_data_p_4));
assert property (ready2 |-> p2_data_p_1 == $past(p1_data_p_2 + p1_data_p_3));

// p3 accumulation from p2
assert property (ready1 |-> p3_data_p_0 == $past(p2_data_p_0 + p2_data_p_1));

// No-X on outputs once inputs have 3-cycle valid history
assert property (ready3 && !$isunknown($past({data_a[15:0], data_b, ddata_in},3))
                 |-> !$isunknown({data_p, ddata_out}));

// Lightweight combinational integrity (sanity on sign-extension and shifts)
assert property (p1_data_a_1p_17_s == {1'b0, data_a[15:0]});
assert property (p1_data_a_1n_17_s == ~p1_data_a_1p_17_s + 1'b1);
assert property (p1_data_a_1p_s == {{7{p1_data_a_1p_17_s[16]}}, p1_data_a_1p_17_s});
assert property (p1_data_a_1n_s == {{7{p1_data_a_1n_17_s[16]}}, p1_data_a_1n_17_s});
assert property (p1_data_a_2p_s == ($signed(p1_data_a_1p_s) <<< 1));
assert property (p1_data_a_2n_s == ($signed(p1_data_a_1n_s) <<< 1));

// Functional coverage (exercise all selection branches)
cover property (data_b[1:0] == 2'b00);
cover property (data_b[1:0] == 2'b01);
cover property (data_b[1:0] == 2'b10);
cover property (data_b[1:0] == 2'b11);

cover property (data_b[3:1] == 3'b000);
cover property (data_b[3:1] == 3'b001);
cover property (data_b[3:1] == 3'b010);
cover property (data_b[3:1] == 3'b011);
cover property (data_b[3:1] == 3'b100);
cover property (data_b[3:1] == 3'b101);
cover property (data_b[3:1] == 3'b110);
cover property (data_b[3:1] == 3'b111);

cover property (data_b[5:3] == 3'b011);
cover property (data_b[5:3] == 3'b100);
cover property (data_b[5:3] == 3'b001);
cover property (data_b[5:3] == 3'b101);
cover property (data_b[5:3] == 3'b000);
cover property (data_b[5:3] == 3'b111);

cover property (data_b[7:5] == 3'b011);
cover property (data_b[7:5] == 3'b100);
cover property (data_b[7:5] == 3'b001);
cover property (data_b[7:5] == 3'b101);
cover property (data_b[7:5] == 3'b000);
cover property (data_b[7:5] == 3'b111);

cover property (data_b[7] == 1'b0);
cover property (data_b[7] == 1'b1);

// Extremes and sign
cover property (data_a[16] == 1'b0 && data_a[15:0] == 16'd0 && data_b == 8'd0);
cover property (data_a[16] == 1'b1 && data_a[15:0] == 16'hFFFF && data_b == 8'hFF);

`endif // ASSERT_ON