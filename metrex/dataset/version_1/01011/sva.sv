// SVA for mux4x1: concise, high-quality checks and coverage
module mux4x1_sva #(parameter SIZE=32) (
  input  logic [SIZE-1:0] iInput0,
  input  logic [SIZE-1:0] iInput1,
  input  logic [SIZE-1:0] iInput2,
  input  logic [SIZE-1:0] iInput3,
  input  logic [1:0]      iSelect,
  input  logic [SIZE-1:0] oOutput
);

  // Sample on any relevant change; use ##0 in consequents to avoid delta races
  clocking cb @(iSelect or iInput0 or iInput1 or iInput2 or iInput3 or oOutput); endclocking
  default clocking cb;

  // Basic sanity: select must be known (prevents unintended latch behavior on X/Z)
  assert property ( !$isunknown(iSelect) )
    else $error("mux4x1: iSelect has X/Z");

  // Core mux functionality
  assert property ( (iSelect == 2'b00) |-> ##0 (oOutput == iInput0) )
    else $error("mux4x1: select 00 mismatch");
  assert property ( (iSelect == 2'b01) |-> ##0 (oOutput == iInput1) )
    else $error("mux4x1: select 01 mismatch");
  assert property ( (iSelect == 2'b10) |-> ##0 (oOutput == iInput2) )
    else $error("mux4x1: select 10 mismatch");
  assert property ( (iSelect == 2'b11) |-> ##0 (oOutput == iInput3) )
    else $error("mux4x1: select 11 mismatch");

  // Output must be known when select and the selected input are known
  assert property (
    (!$isunknown(iSelect) &&
      ((iSelect==2'b00 && !$isunknown(iInput0)) ||
       (iSelect==2'b01 && !$isunknown(iInput1)) ||
       (iSelect==2'b10 && !$isunknown(iInput2)) ||
       (iSelect==2'b11 && !$isunknown(iInput3)))))
    |-> ##0 !$isunknown(oOutput)
  ) else $error("mux4x1: oOutput has X/Z with known select and data");

  // On select change, output must reflect newly selected input immediately (delta)
  assert property (
    $changed(iSelect) |-> ##0 (
      (iSelect==2'b00 && oOutput==iInput0) ||
      (iSelect==2'b01 && oOutput==iInput1) ||
      (iSelect==2'b10 && oOutput==iInput2) ||
      (iSelect==2'b11 && oOutput==iInput3))
  ) else $error("mux4x1: oOutput not updated after iSelect change");

  // Coverage: hit all select values
  cover property ( !$isunknown(iSelect) && iSelect==2'b00 );
  cover property ( !$isunknown(iSelect) && iSelect==2'b01 );
  cover property ( !$isunknown(iSelect) && iSelect==2'b10 );
  cover property ( !$isunknown(iSelect) && iSelect==2'b11 );

  // Coverage: exercise data propagation under each selection
  cover property ( (iSelect==2'b00 && !$isunknown(iInput0)) && $changed(iInput0) ##0 (oOutput==iInput0) );
  cover property ( (iSelect==2'b01 && !$isunknown(iInput1)) && $changed(iInput1) ##0 (oOutput==iInput1) );
  cover property ( (iSelect==2'b10 && !$isunknown(iInput2)) && $changed(iInput2) ##0 (oOutput==iInput2) );
  cover property ( (iSelect==2'b11 && !$isunknown(iInput3)) && $changed(iInput3) ##0 (oOutput==iInput3) );

  // Coverage: observe select transitions
  cover property ( !$isunknown(iSelect) && $changed(iSelect) );

endmodule

// Example bind (instantiate per DUT instance):
// bind mux4x1 mux4x1_sva #(.SIZE(SIZE)) mux4x1_sva_i (.*);