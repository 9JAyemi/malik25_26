module pipereg_w32_sva (
  input logic        clk,
  input logic        resetn,
  input logic        squashn,
  input logic        en,
  input logic [31:0] d,
  input logic [31:0] q
);
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Assertions
  a_clear_on_reset_or_squash: assert property ((!resetn || !squashn) |-> (q == 32'h0));
  a_load_when_en:             assert property ((resetn && squashn && en) |-> (q == d));
  a_hold_when_no_en:          assert property (disable iff (!past_valid)
                                              (resetn && squashn && !en) |-> (q == $past(q)));
  a_change_only_when_allowed: assert property (disable iff (!past_valid)
                                              (q != $past(q)) |-> ((!resetn || !squashn) || (resetn && squashn && en)));
  a_no_x_q:                   assert property (!$isunknown(q));
  a_no_x_ctrl:                assert property (!$isunknown({resetn,squashn,en}));

  // Coverage
  c_reset_clear:   cover property ((!resetn) && (q == 32'h0));
  c_squash_clear:  cover property ((resetn && !squashn) && (q == 32'h0));
  c_both_clear:    cover property ((!resetn && !squashn) && (q == 32'h0));
  c_load:          cover property (resetn && squashn && en && (q == d));
  c_hold:          cover property (disable iff (!past_valid)
                                   (resetn && squashn && !en && (q == $past(q))));
  c_two_loads:     cover property ((resetn && squashn && en && (q == d))
                                   ##1 (resetn && squashn && en && (q == d)));
endmodule

bind pipereg_w32 pipereg_w32_sva sva (
  .clk(clk),
  .resetn(resetn),
  .squashn(squashn),
  .en(en),
  .d(d),
  .q(q)
);