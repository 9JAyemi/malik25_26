// SVA checker for constant_voltage_driver
module constant_voltage_driver_sva #(
  parameter ZERO_VOLT               = 10'b0000000000,
  parameter ONE_POINT_TWO_FIVE_VOLT = 10'b0100000000,
  parameter TWO_POINT_FIVE_VOLT     = 10'b1000000000,
  parameter THREE_POINT_SEVEN_FIVE_VOLT = 10'b1100000000
)(
  input  logic [3:0] data_in,
  input  logic [1:0] mode,
  input  logic [9:0] v_out
);

  // Spec guard: constants must match the intended encodings
  initial begin
    assert (ZERO_VOLT               == 10'b0000000000) else $error("ZERO_VOLT mismatch");
    assert (ONE_POINT_TWO_FIVE_VOLT == 10'b0100000000) else $error("ONE_POINT_TWO_FIVE_VOLT mismatch");
    assert (TWO_POINT_FIVE_VOLT     == 10'b1000000000) else $error("TWO_POINT_FIVE_VOLT mismatch");
    assert (THREE_POINT_SEVEN_FIVE_VOLT == 10'b1100000000) else $error("THREE_POINT_SEVEN_FIVE_VOLT mismatch");
  end

  // Pure combinational spec function
  function automatic logic [9:0] exp_vout (input logic [1:0] m);
    case (m)
      2'b00: exp_vout = ZERO_VOLT;
      2'b01: exp_vout = ONE_POINT_TWO_FIVE_VOLT;
      2'b10: exp_vout = TWO_POINT_FIVE_VOLT;
      2'b11: exp_vout = THREE_POINT_SEVEN_FIVE_VOLT;
      default: exp_vout = ZERO_VOLT;
    endcase
  endfunction

  // Combinational correctness and X/Z checks
  always_comb begin
    assert (!$isunknown(mode)) else $error("mode has X/Z: %b", mode);
    assert (!$isunknown(v_out)) else $error("v_out has X/Z: %b", v_out);
    assert (v_out == exp_vout(mode)) else
      $error("v_out (%b) != expected (%b) for mode %b", v_out, exp_vout(mode), mode);
    assert (v_out inside {ZERO_VOLT, ONE_POINT_TWO_FIVE_VOLT, TWO_POINT_FIVE_VOLT, THREE_POINT_SEVEN_FIVE_VOLT}) else
      $error("v_out took illegal value: %b", v_out);
  end

  // Event for any mode edge (sampling event for concurrent SVA)
  // Use explicit edges to avoid needing a clock
  // Mapping must hold at every mode toggle (same-cycle combinational response)
  property p_map_on_mode_edge;
    @(posedge mode[0] or negedge mode[0] or posedge mode[1] or negedge mode[1])
      1 |-> (v_out == exp_vout(mode));
  endproperty
  assert property (p_map_on_mode_edge);

  // Coverage: hit all modes with correct outputs
  cover property (@(posedge mode[0] or negedge mode[0] or posedge mode[1] or negedge mode[1])
                  mode==2'b00 && v_out==ZERO_VOLT);
  cover property (@(posedge mode[0] or negedge mode[0] or posedge mode[1] or negedge mode[1])
                  mode==2'b01 && v_out==ONE_POINT_TWO_FIVE_VOLT);
  cover property (@(posedge mode[0] or negedge mode[0] or posedge mode[1] or negedge mode[1])
                  mode==2'b10 && v_out==TWO_POINT_FIVE_VOLT);
  cover property (@(posedge mode[0] or negedge mode[0] or posedge mode[1] or negedge mode[1])
                  mode==2'b11 && v_out==THREE_POINT_SEVEN_FIVE_VOLT);

  // Coverage: any mode transition yields correct output (concise transition coverage)
  cover property (@(posedge mode[0] or negedge mode[0] or posedge mode[1] or negedge mode[1])
                  $past(mode) !== mode && v_out == exp_vout(mode));

endmodule

// Bind into DUT
bind constant_voltage_driver constant_voltage_driver_sva #(
  .ZERO_VOLT(ZERO_VOLT),
  .ONE_POINT_TWO_FIVE_VOLT(ONE_POINT_TWO_FIVE_VOLT),
  .TWO_POINT_FIVE_VOLT(TWO_POINT_FIVE_VOLT),
  .THREE_POINT_SEVEN_FIVE_VOLT(THREE_POINT_SEVEN_FIVE_VOLT)
) constant_voltage_driver_sva_i (
  .data_in(data_in),
  .mode(mode),
  .v_out(v_out)
);