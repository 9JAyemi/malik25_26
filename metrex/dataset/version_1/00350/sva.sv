// SVA for barrel_shifter
// Bind this file to the DUT:
//   bind barrel_shifter barrel_shifter_sva #(.bus_size(bus_size), .shift_amount_size(shift_amount_size)) u_sva (.*);

module barrel_shifter_sva #(
  parameter int bus_size = 8,
  parameter int shift_amount_size = 3
)(
  input  logic [bus_size-1:0]            input_bus,
  input  logic [shift_amount_size-1:0]   shift_amount,
  input  logic                           shift_direction,
  input  logic [bus_size-1:0]            output_bus
);

  // Helper
  function automatic bit no_xz_inputs();
    return !$isunknown({shift_direction, shift_amount, input_bus});
  endfunction

  // Core functional correctness (single concise check for both directions)
  property p_func;
    @(input_bus or shift_amount or shift_direction)
      no_xz_inputs()
      |-> output_bus == (shift_direction ? (input_bus << shift_amount)
                                         : (input_bus >> shift_amount));
  endproperty
  assert property (p_func);

  // No X/Z on output when inputs are known
  property p_no_xz_out;
    @(input_bus or shift_amount or shift_direction)
      no_xz_inputs() |-> !$isunknown(output_bus);
  endproperty
  assert property (p_no_xz_out);

  // Identity on zero shift
  property p_zero_shift_identity;
    @(input_bus or shift_amount or shift_direction)
      no_xz_inputs() && (shift_amount == '0) |-> output_bus == input_bus;
  endproperty
  assert property (p_zero_shift_identity);

  // Overshift yields zero (for either direction)
  property p_overshift_zero;
    @(input_bus or shift_amount or shift_direction)
      no_xz_inputs() && ($unsigned(shift_amount) >= bus_size) |-> output_bus == '0;
  endproperty
  assert property (p_overshift_zero);

  // Simple sanity: zero in -> zero out
  property p_zero_in_zero_out;
    @(input_bus or shift_amount or shift_direction)
      no_xz_inputs() && (input_bus == '0) |-> output_bus == '0;
  endproperty
  assert property (p_zero_in_zero_out);

  // Coverage
  cover property (@(input_bus or shift_amount or shift_direction) no_xz_inputs() &&  shift_direction);
  cover property (@(input_bus or shift_amount or shift_direction) no_xz_inputs() && !shift_direction);
  cover property (@(input_bus or shift_amount or shift_direction) no_xz_inputs() && (shift_amount == '0));
  cover property (@(input_bus or shift_amount or shift_direction) no_xz_inputs() && ($unsigned(shift_amount) == 1));
  cover property (@(input_bus or shift_amount or shift_direction) no_xz_inputs() && ($unsigned(shift_amount) == (bus_size-1)));
  cover property (@(input_bus or shift_amount or shift_direction) no_xz_inputs() && ($unsigned(shift_amount) >= bus_size));

endmodule