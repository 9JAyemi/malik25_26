// SVA for top_module and submodules (concise, high-quality checks + coverage)

/////////////////////////////////////////////////////////////
// Assertions bound into counter_4bit
/////////////////////////////////////////////////////////////
module counter_4bit_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  load,
  input logic [3:0]  q
);
  default clocking cb @(posedge clk); endclocking

  // No X on q after reset deasserts
  a_q_known: assert property (!reset |-> !$isunknown(q));

  // Synchronous reset clears q on next edge
  a_reset_clears: assert property (reset |=> q == 4'h0);

  // Load branch (note: RTL compares 8b load to 4b q)
  a_load_branch: assert property (disable iff (reset)
                                  (load != q) |=> q == $past(load[3:0]));

  // Increment branch
  a_inc_branch:  assert property (disable iff (reset)
                                  (load == q) |=> q == ($past(q) + 4'd1));

  // Explicit wrap check on increment branch
  a_wrap:        assert property (disable iff (reset)
                                  (load == q && q == 4'hF) |=> q == 4'h0);

  // Coverage: exercise both branches and the width-mismatch corner
  c_load_branch: cover  property (disable iff (reset) (load != q));
  c_inc_branch:  cover  property (disable iff (reset) (load == q));
  // Corner: low nibble equals q but upper nibble nonzero => load branch taken due to width mismatch
  c_mismatch:    cover  property (disable iff (reset)
                                  (load[3:0] == q && load[7:4] != 4'h0) ##1 (q == $past(load[3:0])));
endmodule

bind counter_4bit counter_4bit_sva u_counter_4bit_sva (.clk(clk), .reset(reset), .load(load), .q(q));

/////////////////////////////////////////////////////////////
// Assertions bound into top_module
/////////////////////////////////////////////////////////////
module top_module_sva (
  input  logic         clk,
  input  logic         reset,
  input  logic [31:0]  in,
  input  logic [3:0]   q,
  input  logic [7:0]   sum_out,
  input  logic [3:0]   count_out,
  input  logic [7:0]   load_value
);
  default clocking cb @(posedge clk); endclocking

  // Output sanity
  a_out_known:    assert property (!reset |-> !$isunknown({q,sum_out}));

  // Internal connectivity
  a_cnt_conn:     assert property (count_out == q);

  // Due to truncation in RTL concat, load_value == in[7:0]
  a_load_is_byte1: assert property (load_value == in[7:0]);

  // Sum correctness (also implicitly checks sum_module connectivity)
  a_sum_ok:       assert property (sum_out == ({4'b0, q} + in[7:0]));

  // Coverage: observe sum overflow
  c_sum_overflow: cover  property (disable iff (reset)
                                   ({1'b0,in[7:0]} + {5'b0,q})[8] == 1'b1);
endmodule

bind top_module top_module_sva u_top_module_sva (
  .clk(clk),
  .reset(reset),
  .in(in),
  .q(q),
  .sum_out(sum_out),
  .count_out(count_out),
  .load_value(load_value)
);