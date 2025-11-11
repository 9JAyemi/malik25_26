// SVA for velocityControlHdl_Dynamic_Saturation
// Combinational sampling using $global_clock to avoid needing a DUT clock.

module velocityControlHdl_Dynamic_Saturation_sva
(
  input  logic signed [17:0] up,
  input  logic signed [35:0] u,
  input  logic signed [17:0] lo,
  input  logic signed [35:0] y,
  input  logic                sat_mode
);

  default clocking cb @($global_clock); endclocking

  function automatic logic signed [35:0] ext18_to36(input logic signed [17:0] s);
    return { {8{s[17]}}, s, 10'b0 };
  endfunction

  logic signed [35:0] up_e, lo_e;
  assign up_e = ext18_to36(up);
  assign lo_e = ext18_to36(lo);

  let lower  = (u < lo_e);
  let upper  = (u > up_e);
  let within = !(lower || upper);

  // Golden functional equivalence
  assert property ( y == (lower ? lo_e : (upper ? up_e : u)) );

  // sat_mode semantics
  assert property ( sat_mode == (lower || upper) );

  // Case-specific checks
  assert property ( lower  |-> (y == lo_e && sat_mode) );
  assert property ( upper  |-> (y == up_e && sat_mode) );
  assert property ( within |-> (y == u   && !sat_mode) );

  // Priority when both sides would trigger (lo_e > up_e corner)
  assert property ( (lower && upper) |-> (y == up_e && sat_mode) );

  // Outputs must be known when inputs are known
  assert property ( (!$isunknown({u,up,lo})) |-> (!$isunknown({y,sat_mode})) );

  // If bounds are well-ordered, output stays within them
  assert property ( (lo_e <= up_e) |-> ((y >= lo_e) && (y <= up_e)) );

  // Coverage
  cover property (lower);
  cover property (upper);
  cover property (within && (u != lo_e) && (u != up_e));
  cover property (u == lo_e && !sat_mode && y == u);
  cover property (u == up_e && !sat_mode && y == u);
  cover property (lower && upper);        // priority corner (lo_e > up_e)
  cover property (lo_e == up_e);          // equal bounds corner

endmodule

// Bind into the DUT (adjust instance/path as needed)
bind velocityControlHdl_Dynamic_Saturation
  velocityControlHdl_Dynamic_Saturation_sva sva_i
  (
    .up(up),
    .u(u),
    .lo(lo),
    .y(y),
    .sat_mode(sat_mode)
  );