// SVA for HardRegister
// Concise, high-quality checks and coverage. Bind this to your DUT.

module HardRegister_sva
  #(parameter int Width        = 32,
    parameter logic [Width-1:0] ResetValue  = {Width{1'b0}},
    parameter logic [Width-1:0] SetValue    = {Width{1'b1}},
    parameter bit AsyncReset    = 0,
    parameter bit AsyncSet      = 0)
  (input  logic                 Clock,
   input  logic                 Reset,
   input  logic                 Set,
   input  logic                 Enable,
   input  logic [Width-1:0]     In,
   input  logic [Width-1:0]     Out);

  // Priority and next-cycle effects sampled on Clock
  // Reset dominates
  assert property (@(posedge Clock) Reset |=> (Out == ResetValue))
    else $error("Out must be ResetValue after Reset asserted");

  // Set takes effect when Reset is low
  assert property (@(posedge Clock) (!Reset && Set) |=> (Out == SetValue))
    else $error("Out must be SetValue when Set asserted without Reset");

  // Enable loads In when neither Reset nor Set are asserted
  assert property (@(posedge Clock) (!Reset && !Set && Enable) |=> (Out == $past(In)))
    else $error("Out must capture In when Enable and no Reset/Set");

  // Explicit Reset-over-Set priority
  assert property (@(posedge Clock) (Reset && Set) |=> (Out == ResetValue))
    else $error("Reset must override Set");

  // Hold behavior (only fully checkable in purely synchronous mode)
  if (!AsyncReset && !AsyncSet) begin
    assert property (@(posedge Clock) (!Reset && !Set && !Enable) |=> (Out == $past(Out)))
      else $error("Out must hold when no control active (sync mode)");

    // Any change to Out must be caused by prior-cycle controls (sync mode)
    assert property (@(posedge Clock)
                     $changed(Out) |-> ($past(Reset) ||
                                        $past(Set) ||
                                        ($past(Enable) && !$past(Reset) && !$past(Set))))
      else $error("Out changed without qualifying control (sync mode)");
  end

  // Sanity: Out known after control actions
  assert property (@(posedge Clock) Reset |=> !$isunknown(Out))
    else $error("Out has X/Z after Reset");
  assert property (@(posedge Clock) (!Reset && Set) |=> !$isunknown(Out))
    else $error("Out has X/Z after Set");
  assert property (@(posedge Clock) (!Reset && !Set && Enable) |=> !$isunknown(Out))
    else $error("Out has X/Z after Enable load");

  // Coverage
  cover property (@(posedge Clock) Reset ##1 (Out == ResetValue));
  cover property (@(posedge Clock) (!Reset && Set) ##1 (Out == SetValue));
  cover property (@(posedge Clock) (!Reset && !Set && Enable) ##1 (Out == $past(In)));
  cover property (@(posedge Clock) (Reset && Set) ##1 (Out == ResetValue));
  if (!AsyncReset && !AsyncSet)
    cover property (@(posedge Clock) (!Reset && !Set && !Enable) ##1 (Out == $past(Out)));

  // Observe async edges when enabled (for coverage)
  if (AsyncReset) cover property (@(posedge Reset) 1);
  if (AsyncSet)   cover property (@(posedge Set)    1);

endmodule

// Bind into the DUT (parameters are picked up from the instance)
bind HardRegister HardRegister_sva #(
  .Width(Width),
  .ResetValue(ResetValue),
  .SetValue(SetValue),
  .AsyncReset(AsyncReset),
  .AsyncSet(AsyncSet)
) u_HardRegister_sva (
  .Clock(Clock),
  .Reset(Reset),
  .Set(Set),
  .Enable(Enable),
  .In(In),
  .Out(Out)
);