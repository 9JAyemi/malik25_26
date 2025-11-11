// SVA for top_module
// Bind these assertions to the DUT. Focus on correctness, concision, and meaningful coverage.

module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  in,
  input  logic        select,
  input  logic [3:0]  counter_out,
  input  logic [7:0]  edge_out,
  input  logic [7:0]  and_out,

  // internal observability
  input  logic [3:0]  counter_reg,
  input  logic [7:0]  edge_reg,
  input  logic [7:0]  edge_out_reg,
  input  logic [7:0]  and_out_reg
);

  default clocking cb @(posedge clk); endclocking

  // Counter: reset and increment
  a_cnt_reset: assert property (reset |-> counter_out == 4'h0);
  a_cnt_inc:   assert property (disable iff (reset) counter_out == $past(counter_out) + 1);
  a_cnt_no_x:  assert property (disable iff (reset) !$isunknown(counter_out));
  c_cnt_wrap:  cover  property (disable iff (reset) $past(counter_out)==4'hF && counter_out==4'h0);

  // Counter outputs mirror regs (observability)
  a_cnt_out_matches_reg:  assert property (counter_out == counter_reg);

  // Edge shifter: expect 1-bit shift-in (LSB of 'in'); catches width/concat issues
  a_edge_shift: assert property (disable iff (reset)
                                 edge_reg == {$past(edge_reg[6:0]), in[0]});

  // Edge detector behavior: sticky set to 0xFF on bit[7]!=bit[6], else hold last
  a_edge_fire:  assert property ((edge_reg[7] != edge_reg[6]) |-> edge_out == 8'hFF);
  a_edge_hold:  assert property ((edge_reg[7] == edge_reg[6]) |-> edge_out == $past(edge_out));
  a_edge_sticky:assert property ($past(edge_out)==8'hFF |-> edge_out==8'hFF);
  a_edge_known_on_fire: assert property ((edge_reg[7] != edge_reg[6]) |-> !$isunknown(edge_out));

  // Edge output mirrors reg (observability)
  a_edge_out_matches_reg: assert property (edge_out == edge_out_reg);

  // Functional AND: gating and width-extension correctness
  a_sel0_zero:      assert property (!select |-> and_out == 8'h00);
  a_sel1_top_zero:  assert property ( select |-> and_out[7:4] == 4'h0);
  a_sel1_low_match: assert property ( select |-> and_out[3:0] == (edge_out[3:0] & counter_out));
  a_and_no_x_when_zero: assert property (!select |-> !$isunknown(and_out));

  // Functional output mirrors reg (observability)
  a_and_out_matches_reg: assert property (and_out == and_out_reg);

  // Useful coverage
  c_edge_event_sets_ff: cover property ((edge_reg[7]!=edge_reg[6]) ##1 edge_out==8'hFF);
  c_select_useful_and:  cover property (select && (edge_out[3:0]!=4'h0) && (counter_out!=4'h0)
                                        ##1 (and_out[3:0] != 4'h0));
  c_select_toggle:      cover property (!select ##1 select ##1 !select);

endmodule

// Bind into DUT (connect internal regs for observability)
bind top_module top_module_sva sva_i (
  .clk(clk),
  .reset(reset),
  .in(in),
  .select(select),
  .counter_out(counter_out),
  .edge_out(edge_out),
  .and_out(and_out),
  .counter_reg(counter_reg),
  .edge_reg(edge_reg),
  .edge_out_reg(edge_out_reg),
  .and_out_reg(and_out_reg)
);