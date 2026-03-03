// SVA for v89d234_v9148cb (register with load-enable)
module v89d234_v9148cb_sva (
  input logic        clk,
  input logic        load,
  input logic [7:0]  d,
  input logic [7:0]  q
);
  bit past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Sanity: no X/Z on sampled signals
  assert property (!$isunknown({load, d, q}));

  // Functional correctness
  assert property (load  |=> q == $past(d));     // capture on load
  assert property (!load |=> q == $past(q));     // hold when not loading
  assert property ((q != $past(q)) |-> $past(load)); // any change implies prior load
  assert property (load && (d == q) |=> q == $past(q)); // loading same value doesn't change q

  // Coverage
  cover property (load);
  cover property (!load);
  cover property (load ##1 (q == $past(d)));
  cover property (!load ##1 (q == $past(q)));
  cover property (load ##1 load); // back-to-back loads
endmodule

bind v89d234_v9148cb v89d234_v9148cb_sva i_v9148cb_sva (
  .clk (clk),
  .load(load),
  .d   (d),
  .q   (q)
);


// Top-level connectivity and end-to-end checks
module v89d234_top_sva (
  input  logic        clk,
  input  logic [7:0]  in_d,
  input  logic        load,
  input  logic [7:0]  out_q,
  input  logic [7:0]  inst_d,
  input  logic [7:0]  inst_q,
  input  logic        inst_clk,
  input  logic        inst_load
);
  bit past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Connectivity (also implicitly checks the [0:7]/[7:0] bit-ordering resolves correctly end-to-end)
  assert property (in_d     == inst_d);
  assert property (load     == inst_load);
  assert property (clk      == inst_clk);
  assert property (out_q    == inst_q);

  // IO sanity
  assert property (!$isunknown({clk, load, in_d, out_q}));

  // End-to-end functional check at top
  assert property (load |=> out_q == $past(in_d));

  // Coverage
  cover property (load ##1 (out_q == $past(in_d)));
  cover property (!load ##1 (out_q == $past(out_q)));
endmodule

bind v89d234 v89d234_top_sva i_top_sva (
  .clk      (v41eb95),
  .in_d     (v39f831),
  .load     (vf892a0),
  .out_q    (vb1c024),
  .inst_d   (v9148cb.d),
  .inst_q   (v9148cb.q),
  .inst_clk (v9148cb.clk),
  .inst_load(v9148cb.load)
);