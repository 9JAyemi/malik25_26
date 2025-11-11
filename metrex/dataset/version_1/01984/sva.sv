// SVA for InputCell
module InputCell_sva (
  input  logic InputPin,
  input  logic FromPreviousBSCell,
  input  logic CaptureDR,
  input  logic ShiftDR,
  input  logic TCK,
  input  logic Latch,
  input  logic ToNextBSCell
);
  default clocking cb_pos @(posedge TCK); endclocking

  // Correct data captured into Latch on posedge
  property p_capture_path;
    CaptureDR |=> (Latch == $past(InputPin));
  endproperty
  assert property (p_capture_path);

  property p_shift_path;
    (!CaptureDR && ShiftDR) |=> (Latch == $past(FromPreviousBSCell));
  endproperty
  assert property (p_shift_path);

  // Hold when idle
  property p_hold_idle;
    !(CaptureDR || ShiftDR) |=> (Latch == $past(Latch));
  endproperty
  assert property (p_hold_idle);

  // Latch only changes when enabled
  property p_change_guard;
    $changed(Latch) |-> $past(CaptureDR || ShiftDR);
  endproperty
  assert property (p_change_guard);

  // Forward Latch to ToNextBSCell on following negedge
  property p_forward_halfcycle;
    1 |=> ($past(ToNextBSCell, 1, negedge TCK) == $past(Latch));
  endproperty
  assert property (p_forward_halfcycle);

  // If both asserted, InputPin must be selected
  property p_both_high_prefers_input;
    (CaptureDR && ShiftDR) |=> (Latch == $past(InputPin));
  endproperty
  assert property (p_both_high_prefers_input);

  // Coverage
  cover property (@(posedge TCK) CaptureDR ##1 @(negedge TCK) ToNextBSCell == $past(InputPin));
  cover property (@(posedge TCK) (!CaptureDR && ShiftDR) ##1 @(negedge TCK) ToNextBSCell == $past(FromPreviousBSCell));
  cover property (@(posedge TCK) (CaptureDR && ShiftDR));
  cover property (@(posedge TCK) !(CaptureDR || ShiftDR));
endmodule

// Bind into DUT (connect internal Latch)
bind InputCell InputCell_sva sva_InputCell (
  .InputPin(InputPin),
  .FromPreviousBSCell(FromPreviousBSCell),
  .CaptureDR(CaptureDR),
  .ShiftDR(ShiftDR),
  .TCK(TCK),
  .Latch(Latch),
  .ToNextBSCell(ToNextBSCell)
);