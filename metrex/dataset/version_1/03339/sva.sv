// SVA for min_shift
module min_shift_sva (
  input  logic         clk,
  input  logic         reset,     // synchronous, active-high
  input  logic         select,
  input  logic [7:0]   a,b,c,d,
  input  logic [1:0]   ena,
  input  logic [99:0]  data,
  input  logic [7:0]   min,
  input  logic [99:0]  q
);

  function automatic logic [7:0] f_min4_lt (logic [7:0] aa, bb, cc, dd);
    logic [7:0] min1, min2;
    begin
      min1 = (aa < bb) ? aa : bb;   // tie -> bb
      min2 = (cc < dd) ? cc : dd;   // tie -> dd
      return (min1 < min2) ? min1 : min2; // tie -> min2
    end
  endfunction

  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (reset |=> min == 8'd0)
    else $error("min not cleared on reset");
  assert property (reset |=> q == $past(q))
    else $error("q changed during reset");

  // Min-path: update when select=1
  assert property (disable iff (reset)
                   select |=> min == f_min4_lt($past(a),$past(b),$past(c),$past(d)))
    else $error("min wrong when select=1");

  // Min forced to 0 when select=0
  assert property (disable iff (reset)
                   !select |=> min == 8'd0)
    else $error("min not zero when select=0");

  // Shift/register-path (active when select=0)
  // shift left
  assert property (disable iff (reset)
                   (!select && ena==2'b00) |=> q == { $past(q)[98:0], 1'b0 })
    else $error("q left-shift mismatch");
  // shift right
  assert property (disable iff (reset)
                   (!select && ena==2'b01) |=> q == { 1'b0, $past(q)[99:1] })
    else $error("q right-shift mismatch");
  // load
  assert property (disable iff (reset)
                   (!select && ena==2'b10) |=> q == $past(data))
    else $error("q load mismatch");
  // no-op for ena==11
  assert property (disable iff (reset)
                   (!select && ena==2'b11) |=> q == $past(q))
    else $error("q changed on ena==2'b11");

  // q must not change when select=1 (min-path)
  assert property (disable iff (reset)
                   select |=> q == $past(q))
    else $error("q changed when select=1");

  // Simple functional coverage
  cover property (reset);
  cover property (disable iff (reset) select);
  cover property (disable iff (reset) !select && ena==2'b00);
  cover property (disable iff (reset) !select && ena==2'b01);
  cover property (disable iff (reset) !select && ena==2'b10);
  cover property (disable iff (reset) !select && ena==2'b11);

endmodule

// Bind into DUT
bind min_shift min_shift_sva sva_i (
  .clk(clk), .reset(reset), .select(select),
  .a(a), .b(b), .c(c), .d(d),
  .ena(ena), .data(data), .min(min), .q(q)
);