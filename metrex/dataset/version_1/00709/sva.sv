// SVA for barrel_shifter
// Bind-in checker; pure combinational functional checks + concise coverage

module barrel_shifter_sva #(parameter WIDTH=8, SAW=3)
(
  input  logic [WIDTH-1:0] data_in,
  input  logic [SAW-1:0]   shift_amount,
  input  logic             shift_direction,
  input  logic [WIDTH-1:0] data_out
);

  // Event to sample on any input change
  event any_change_ev;
  always @ (data_in or shift_amount or shift_direction) -> any_change_ev;

  // Event to detect output change (sanity: no spurious output toggles)
  event out_change_ev;
  always @ (data_out) -> out_change_ev;

  // Reference model
  function automatic logic [WIDTH-1:0] ref_shift(input logic [WIDTH-1:0] d,
                                                 input logic [SAW-1:0]   a,
                                                 input logic             dir);
    ref_shift = dir ? (d << a) : (d >> a);
  endfunction

  // Functional equivalence when inputs are known
  property p_func;
    @(any_change_ev)
      !$isunknown({data_in, shift_amount, shift_direction})
      |-> (data_out == ref_shift(data_in, shift_amount, shift_direction));
  endproperty
  assert property (p_func)
    else $error("barrel_shifter mismatch: dir=%0b amt=%0d din=%0h dout=%0h exp=%0h",
                shift_direction, shift_amount, data_in, data_out,
                ref_shift(data_in, shift_amount, shift_direction));

  // Shift-by-zero is identity
  assert property (@(any_change_ev)
                   !$isunknown({data_in, shift_amount, shift_direction}) && (shift_amount==0)
                   |-> (data_out == data_in))
    else $error("barrel_shifter: shift_amount==0 but dout!=din");

  // Zero-fill checks
  // Left shift: lower shift_amount bits must be zero (when shift_amount>0)
  assert property (@(any_change_ev)
                   !$isunknown({data_in, shift_amount, shift_direction}) &&
                   shift_direction && (shift_amount>0)
                   |-> (data_out[shift_amount-1:0] == '0))
    else $error("barrel_shifter: left shift zero-fill failed");

  // Right shift: upper shift_amount bits must be zero (when shift_amount>0)
  assert property (@(any_change_ev)
                   !$isunknown({data_in, shift_amount, shift_direction}) &&
                   !shift_direction && (shift_amount>0)
                   |-> (data_out[WIDTH-1 -: shift_amount] == '0))
    else $error("barrel_shifter: right shift zero-fill failed");

  // No spurious output change without input change
  assert property (@(out_change_ev) $changed({data_in, shift_amount, shift_direction}))
    else $error("barrel_shifter: dout changed without input change");

  // Coverage: directions x key shift amounts
  cover property (@(any_change_ev) (shift_direction==0) && (shift_amount==0));
  cover property (@(any_change_ev) (shift_direction==1) && (shift_amount==0));
  cover property (@(any_change_ev) (shift_direction==0) && (shift_amount==1));
  cover property (@(any_change_ev) (shift_direction==1) && (shift_amount==1));
  cover property (@(any_change_ev) (shift_direction==0) && (shift_amount==7));
  cover property (@(any_change_ev) (shift_direction==1) && (shift_amount==7));

  // Coverage: bit-drop at MSB/LSB on nonzero shifts
  cover property (@(any_change_ev)
                  shift_direction && (shift_amount>0) && data_in[WIDTH-1] && (data_out[WIDTH-1]==1'b0));
  cover property (@(any_change_ev)
                  !shift_direction && (shift_amount>0) && data_in[0] && (data_out[0]==1'b0));

endmodule

bind barrel_shifter barrel_shifter_sva #(.WIDTH(8), .SAW(3)) u_barrel_shifter_sva (.*);