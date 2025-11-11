// SVA checkers and binds for top_module and mux_2to1

// Checker for top_module
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  d1,
  input  logic [7:0]  d2,
  input  logic        sel,
  input  logic [7:0]  q,
  input  logic [3:0]  count,
  input  logic [7:0]  mux_out,
  input  logic [7:0]  sum
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (reset |=> count == 4'd0);
  assert property (reset && $past(reset) |-> count == 4'd0 && $stable(count));

  // Increment behavior (and first count after reset deassert)
  assert property (!reset && !$past(reset) |-> count == $past(count) + 4'd1);
  assert property ($past(reset) && !reset |-> count == 4'd1);

  // Wrap-around
  assert property (!reset && !$past(reset) && $past(count) == 4'hF |-> count == 4'd0);

  // Mux correctness at top (structural wiring to mux_2to1)
  assert property (mux_out == (sel ? d2 : d1));

  // Sum correctness and output tie-off
  assert property (sum == mux_out + {4'b0, count});
  assert property (q == sum);
  assert property (q == (sel ? d2 : d1) + {4'b0, count});

  // Knownness after reset released
  assert property (!reset |-> !$isunknown({count, mux_out, sum, q, sel}));

  // Coverage
  cover property (reset ##1 !reset);
  cover property (!reset && sel == 1'b0);
  cover property (!reset && sel == 1'b1);
  cover property (!reset && $changed(sel));
  cover property (!reset ##1 count == 4'hF ##1 !reset ##1 count == 4'h0); // wrap w/o reset
  cover property (!reset && (({1'b0, mux_out} + {1'b0, count})[8] == 1'b1)); // add carry out
  cover property (!reset && sel == 1'b0 && q == d1 + {4'b0, count});
  cover property (!reset && sel == 1'b1 && q == d2 + {4'b0, count});
endmodule

bind top_module top_module_sva top_module_sva_i (
  .clk(clk),
  .reset(reset),
  .d1(d1),
  .d2(d2),
  .sel(sel),
  .q(q),
  .count(count),
  .mux_out(mux_out),
  .sum(sum)
);

// Lightweight functional checker for mux_2to1
module mux_2to1_sva (
  input logic [7:0] a,
  input logic [7:0] b,
  input logic       sel,
  input logic [7:0] out
);
  // Combinational functional equivalence and knownness
  always @* begin
    assert (out == (sel ? b : a))
      else $error("mux_2to1 functional mismatch");
    if (!$isunknown({a,b,sel}))
      assert (!$isunknown(out))
        else $error("mux_2to1 X/Z propagation");
  end
endmodule

bind mux_2to1 mux_2to1_sva mux_2to1_sva_i (
  .a(a), .b(b), .sel(sel), .out(out)
);