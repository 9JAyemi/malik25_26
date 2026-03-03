// SVA for MUX16X4 — concise, high-quality checks and coverage
// Bind these assertions to the DUT

module MUX16X4_sva
(
  input logic [15:0] iInput0,
  input logic [15:0] iInput1,
  input logic [15:0] iInput2,
  input logic [15:0] iInput3,
  input logic [1:0]  iSelect,
  input logic [15:0] oOutput
);

  function automatic logic [15:0] sel_data(
    input logic [1:0]  s,
    input logic [15:0] d0, d1, d2, d3
  );
    case (s)
      2'b00: sel_data = d0;
      2'b01: sel_data = d1;
      2'b10: sel_data = d2;
      2'b11: sel_data = d3;
      default: sel_data = 'x;
    endcase
  endfunction

  // Select must be known (prevents latchy behavior on X/Z select)
  assert property (!$isunknown(iSelect))
    else $error("MUX16X4: iSelect has X/Z");

  // Functional correctness: when select is known, output matches selected input
  assert property (!$isunknown(iSelect) |-> (oOutput === sel_data(iSelect,iInput0,iInput1,iInput2,iInput3)))
    else $error("MUX16X4: functional mismatch for selected input");

  // Zero-delay response on any driving change
  assert property ( ($changed(iSelect) || $changed(iInput0) || $changed(iInput1) || $changed(iInput2) || $changed(iInput3))
                    |-> ##0 (oOutput === sel_data(iSelect,iInput0,iInput1,iInput2,iInput3)) )
    else $error("MUX16X4: output not updated in same delta");

  // No X on output when path is fully known
  assert property ( (!$isunknown(iSelect) && !$isunknown(sel_data(iSelect,iInput0,iInput1,iInput2,iInput3)))
                    |-> (!$isunknown(oOutput) && (oOutput == sel_data(iSelect,iInput0,iInput1,iInput2,iInput3))) )
    else $error("MUX16X4: unexpected X/Z on output with known select/data");

  // Per-select functional covers (hit each data path)
  cover property (iSelect==2'b00 && (oOutput === iInput0));
  cover property (iSelect==2'b01 && (oOutput === iInput1));
  cover property (iSelect==2'b10 && (oOutput === iInput2));
  cover property (iSelect==2'b11 && (oOutput === iInput3));

  // Exercise dynamic propagation on selected path (data change causes output change in same delta)
  cover property ( (iSelect==2'b00 && $changed(iInput0)) ##0 $changed(oOutput) );
  cover property ( (iSelect==2'b01 && $changed(iInput1)) ##0 $changed(oOutput) );
  cover property ( (iSelect==2'b10 && $changed(iInput2)) ##0 $changed(oOutput) );
  cover property ( (iSelect==2'b11 && $changed(iInput3)) ##0 $changed(oOutput) );

  // Cover seeing all four selects (order-agnostic)
  cover property (! $isunknown(iSelect));
endmodule

bind MUX16X4 MUX16X4_sva sva_mux16x4 (
  .iInput0(iInput0),
  .iInput1(iInput1),
  .iInput2(iInput2),
  .iInput3(iInput3),
  .iSelect(iSelect),
  .oOutput(oOutput)
);