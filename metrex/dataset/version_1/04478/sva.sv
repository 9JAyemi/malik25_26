// SVA checker for shifter. Bind into the DUT.
// Uses $global_clock so it works for combinational DUTs.
module shifter_sva(
  input  logic [33:0] in,
  input  logic [15:0] out,
  input  logic [7:0]  shift,
  input  logic [15:0] quotient,
  input  logic [15:0] remainder,
  input  logic [18:0] msbs,
  input  logic        in_range,
  input  logic [15:0] out_unclipped
);

  default clocking cb @(posedge $global_clock); endclocking

  // Golden functions
  function automatic logic [15:0] q_exp(input logic [33:0] i, input logic [7:0] s);
    return (s <= 8'd18) ? ((i >> s)[15:0]) : i[15:0];
  endfunction

  function automatic logic [15:0] r_exp(input logic [33:0] i, input logic [7:0] s);
    if (s <= 8'd15) return (((i & ((34'h1 << s) - 1)) << (16 - s))[15:0]);
    else if (s <= 8'd18) return ((i >> (s - 16))[15:0]);
    else return 16'h0;
  endfunction

  function automatic logic [18:0] msbs_exp(input logic [33:0] i, input logic [7:0] s);
    return (s <= 8'd18) ? ( $signed(i[33:15]) >>> s ) : i[33:15];
  endfunction

  function automatic logic        in_range_exp(input logic [18:0] m);
    return (&m) | ~(|m);
  endfunction

  function automatic logic [15:0] out_unclipped_exp(input logic [15:0] q, input logic [15:0] r, input logic sgn);
    return q + (sgn & (|r));
  endfunction

  function automatic logic [15:0] sat_exp(input logic [15:0] u, input logic ir, input logic sgn);
    return ir ? u : {sgn, {15{~sgn}}};
  endfunction

  // X checks on inputs
  assert property ( !$isunknown({in,shift}) );

  // Structural equivalence checks
  assert property ( quotient      == q_exp(in, shift) );
  assert property ( remainder     == r_exp(in, shift) );
  assert property ( msbs          == msbs_exp(in, shift) );
  assert property ( in_range      == in_range_exp(msbs) );
  assert property ( out_unclipped == out_unclipped_exp(quotient, remainder, in[33]) );
  assert property ( out           == sat_exp(out_unclipped, in_range, in[33]) );

  // Corner consistency with case defaults
  assert property ( (shift > 8'd18) |-> (quotient == in[15:0] && remainder == 16'h0 && msbs == in[33:15]) );
  assert property ( (shift == 8'd0) |-> (remainder == 16'h0 && msbs == in[33:15]) );
  assert property ( (shift == 8'd18) |-> (quotient == in[33:18] && remainder == in[17:2] && msbs == { {18{in[33]}}, in[33]} ) );

  // Saturation checks
  assert property ( (!in_range && !in[33]) |-> (out == 16'h7FFF) );
  assert property ( (!in_range &&  in[33]) |-> (out == 16'h8000) );

  // Coverage
  cover property ( shift inside {[0:18]} );
  cover property ( shift > 18 );
  cover property ( in[33] && (remainder != 16'h0) && in_range && (out_unclipped == quotient + 1) );
  cover property ( !in[33] && (remainder != 16'h0) && in_range && (out_unclipped == quotient) );
  cover property ( !in_range && !in[33] && out == 16'h7FFF );
  cover property ( !in_range &&  in[33] && out == 16'h8000 );
  cover property ( shift == 0 );
  cover property ( shift == 15 );
  cover property ( shift == 16 );
  cover property ( shift == 18 );

endmodule

// Bind into all shifter instances
bind shifter shifter_sva u_shifter_sva(
  .in(in),
  .out(out),
  .shift(shift),
  .quotient(quotient),
  .remainder(remainder),
  .msbs(msbs),
  .in_range(in_range),
  .out_unclipped(out_unclipped)
);