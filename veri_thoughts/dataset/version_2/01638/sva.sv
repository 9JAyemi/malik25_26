module mux_4to1_enable_sva (
  input logic [3:0] in,
  input logic [1:0] sel,
  input logic enable,
  input logic out
);

  // When disabled, out must be 0.
  check_out_zero_when_disabled: assert property (
    @(posedge enable or negedge enable
      or posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1]
      or posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1]
      or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
    (enable == 1'b0) |-> (out == 1'b0)
  );

  // When enabled and sel==00, out equals in[0].
  check_sel_00_mapping: assert property (
    @(posedge enable or negedge enable
      or posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1]
      or posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1]
      or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
    (enable && (sel == 2'b00)) |-> (out == in[0])
  );

  // When enabled and sel==01, out equals in[1].
  check_sel_01_mapping: assert property (
    @(posedge enable or negedge enable
      or posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1]
      or posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1]
      or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
    (enable && (sel == 2'b01)) |-> (out == in[1])
  );

  // When enabled and sel==10, out equals in[2].
  check_sel_10_mapping: assert property (
    @(posedge enable or negedge enable
      or posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1]
      or posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1]
      or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
    (enable && (sel == 2'b10)) |-> (out == in[2])
  );

  // When enabled and sel==11, out equals in[3].
  check_sel_11_mapping: assert property (
    @(posedge enable or negedge enable
      or posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1]
      or posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1]
      or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
    (enable && (sel == 2'b11)) |-> (out == in[3])
  );

  // When enabled and sel is not 00/01/10/11 (X/Z), out is 0.
  check_unknown_sel_defaults_zero: assert property (
    @(posedge enable or negedge enable
      or posedge sel[0] or negedge sel[0] or posedge sel[1] or negedge sel[1]
      or posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1]
      or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
    (enable && (sel !== 2'b00) && (sel !== 2'b01) && (sel !== 2'b10) && (sel !== 2'b11)) |-> (out == 1'b0)
  );

  // On rising edge of enable, out reflects selected input (or 0 if sel is X/Z).
  check_out_on_enable_rise: assert property (
    @(posedge enable)
      1'b1 |-> (
        (sel == 2'b00 && out == in[0]) ||
        (sel == 2'b01 && out == in[1]) ||
        (sel == 2'b10 && out == in[2]) ||
        (sel == 2'b11 && out == in[3]) ||
        ((sel !== 2'b00) && (sel !== 2'b01) && (sel !== 2'b10) && (sel !== 2'b11) && (out == 1'b0))
      )
  );

  // On falling edge of enable, out must be 0.
  check_out_on_enable_fall_zero: assert property (
    @(negedge enable) 1'b1 |-> (out == 1'b0)
  );

  // Changing in[0] while enabled with sel not 00 does not change out.
  check_unselected_in0_no_effect: assert property (
    @(posedge in[0] or negedge in[0])
    (enable && ((sel == 2'b01) || (sel == 2'b10) || (sel == 2'b11))) |-> $stable(out)
  );

  // Changing in[1] while enabled with sel not 01 does not change out.
  check_unselected_in1_no_effect: assert property (
    @(posedge in[1] or negedge in[1])
    (enable && ((sel == 2'b00) || (sel == 2'b10) || (sel == 2'b11))) |-> $stable(out)
  );

  // Changing in[2] while enabled with sel not 10 does not change out.
  check_unselected_in2_no_effect: assert property (
    @(posedge in[2] or negedge in[2])
    (enable && ((sel == 2'b00) || (sel == 2'b01) || (sel == 2'b11))) |-> $stable(out)
  );

  // Changing in[3] while enabled with sel not 11 does not change out.
  check_unselected_in3_no_effect: assert property (
    @(posedge in[3] or negedge in[3])
    (enable && ((sel == 2'b00) || (sel == 2'b01) || (sel == 2'b10))) |-> $stable(out)
  );

endmodule