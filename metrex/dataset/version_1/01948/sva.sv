// SVA checkers for barrel_shifter
// Bind this checker to the DUT
bind barrel_shifter barrel_shifter_sva bsh_sva();

module barrel_shifter_sva;

  // X/Z checks on inputs
  always_comb begin
    assert (!$isunknown(data_in))        else $error("barrel_shifter: X/Z on data_in");
    assert (!$isunknown(shift_amount))   else $error("barrel_shifter: X/Z on shift_amount");
    assert (!$isunknown(direction_left)) else $error("barrel_shifter: X/Z on direction_left");
  end

  // Internal combinational pipeline consistency
  always_comb begin
    assert (shift_reg[1] == data_in)           else $error("shift_reg[1] != data_in");
    assert (shift_reg[2] == (data_in << 1))    else $error("shift_reg[2] != data_in<<1");
    assert (shift_reg[3] == (data_in << 2))    else $error("shift_reg[3] != data_in<<2");
  end

  // Functional correctness of data_out
  always_comb begin
    unique case (shift_amount)
      2'b00: assert (data_out == data_in)            else $error("out != in");
      2'b01: assert (data_out == (data_in << 1))     else $error("out != in<<1");
      2'b10: assert (data_out == (data_in << 2))     else $error("out != in<<2");
      2'b11: begin
        if (direction_left)
          assert (data_out == (data_in << 2))        else $error("out != in<<2 (dir_left)");
        else
          assert (data_out == data_in)               else $error("out != in (dir_right)");
      end
    endcase
  end

  // Direction is irrelevant unless shift_amount==2'b11
  property dir_independent;
    (shift_amount != 2'b11 && $changed(direction_left)) |-> $stable(data_out);
  endproperty
  assert property (dir_independent);

  // Pure combinational behavior: output stable if inputs stable
  property comb_no_glitch;
    $stable(data_in) && $stable(shift_amount) && $stable(direction_left) |-> $stable(data_out);
  endproperty
  assert property (comb_no_glitch);

  // Any output change must be due to an input/control change
  property output_change_has_cause;
    $changed(data_out) |-> ($changed(data_in) || $changed(shift_amount) || $changed(direction_left));
  endproperty
  assert property (output_change_has_cause);

  // Coverage: hit all functional branches
  cover property (shift_amount == 2'b00 && data_out == data_in);
  cover property (shift_amount == 2'b01 && data_out == (data_in << 1));
  cover property (shift_amount == 2'b10 && data_out == (data_in << 2));
  cover property (shift_amount == 2'b11 && !direction_left && data_out == data_in);
  cover property (shift_amount == 2'b11 &&  direction_left && data_out == (data_in << 2));
  cover property ($changed(direction_left) && shift_amount != 2'b11);

endmodule