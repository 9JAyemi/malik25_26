// SVA for multiply_and_min
// Bind into DUT; focuses on key correctness, reset behavior, and branch/tie coverage.
module multiply_and_min_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  in1, in2,
  input  logic [7:0]  a, b, c, d,
  input  logic [15:0] out,
  input  logic [7:0]  out_lo,
  input  logic [7:0]  final_out
);

  // Expected min expression (matches DUT tie-breaking A>B>C>D)
  function automatic logic [7:0] exp_min(input logic [7:0] a,b,c,d);
    if (a <= b && a <= c && a <= d)      exp_min = a;
    else if (b <= c && b <= d)           exp_min = b;
    else if (c <= d)                     exp_min = c;
    else                                 exp_min = d;
  endfunction

  // Basic sanity: outputs known when not in reset
  assert property (@(posedge clk) !reset |-> !$isunknown({out,out_lo,final_out}));

  // Reset behavior
  assert property (@(posedge clk) reset |-> (out == 16'h0 && out_lo == 8'h0));

  // Multiplier/accumulator step semantics
  // out = zero-extended product + (prev out_lo << 8)
  // out_lo = low byte of product
  assert property (@(posedge clk) disable iff (reset)
    out == ({8'h0,$past(in1)} * {8'h0,$past(in2)}) + ({8'h0,$past(out_lo)} << 8)
      && out_lo == ({8'h0,$past(in1)} * {8'h0,$past(in2)})[7:0]
  );

  // Consequence: low byte consistency
  assert property (@(posedge clk) disable iff (reset) out_lo == out[7:0]);

  // If previous low accumulator was zero, output equals pure product
  assert property (@(posedge clk) disable iff (reset)
    ($past(out_lo) == 8'h00) |-> out == ({8'h0,$past(in1)} * {8'h0,$past(in2)})
  );

  // Min + add correctness observed at clock edge
  assert property (@(posedge clk)
    final_out == (exp_min(a,b,c,d) + out_lo)
  );

  // --------------------------------
  // Coverage
  // --------------------------------

  // Reset release
  cover property (@(posedge clk) $fell(reset));

  // Product corner cases
  cover property (@(posedge clk) disable iff (reset)
    ($past(in1) == 8'h00 || $past(in2) == 8'h00) && out_lo == 8'h00);
  cover property (@(posedge clk) disable iff (reset)
    ($past(in1) == 8'hFF && $past(in2) == 8'hFF));

  // Accumulator contribution and potential overflow into high byte
  cover property (@(posedge clk) disable iff (reset)
    $past(out_lo) != 8'h00 &&
    (({8'h0,$past(in1)} * {8'h0,$past(in2)})[15:8] + $past(out_lo)) > 8'hFF
  );

  // Min branch selections
  cover property (@(posedge clk) exp_min(a,b,c,d) == a);
  cover property (@(posedge clk) exp_min(a,b,c,d) == b);
  cover property (@(posedge clk) exp_min(a,b,c,d) == c);
  cover property (@(posedge clk) exp_min(a,b,c,d) == d);

  // Tie-precedence coverage
  cover property (@(posedge clk) (a==b) && (a<=c) && (a<=d) && (exp_min(a,b,c,d)==a));
  cover property (@(posedge clk) (b==c) && (b< a) && (b<=d) && (exp_min(a,b,c,d)==b));
  cover property (@(posedge clk) (c==d) && (c< a) && (c< b)  && (exp_min(a,b,c,d)==c));

endmodule

bind multiply_and_min multiply_and_min_sva sva_inst (.*);