// SVA for FourToSeven
// Bindable checker with concise but complete functional checks and coverage.

module FourToSeven_sva (
  input  logic [3:0] ByteIn,
  input  logic       Enable,
  input  logic       Polarity,
  input  logic [6:0] SegOut
);

  // Sample on any relevant change
  event comb_ev;
  always @(ByteIn or Enable or Polarity or SegOut) -> comb_ev;
  default clocking cb @ (comb_ev); endclocking

  // Reference model (non-inverted code)
  function automatic logic [6:0] map_noninv (input logic [3:0] b);
    case (b)
      4'd0:  map_noninv = 7'd63;
      4'd1:  map_noninv = 7'd6;
      4'd2:  map_noninv = 7'd91;
      4'd3:  map_noninv = 7'd79;
      4'd4:  map_noninv = 7'd102;
      4'd5:  map_noninv = 7'd109;
      4'd6:  map_noninv = 7'd125;
      4'd7:  map_noninv = 7'd7;
      4'd8:  map_noninv = 7'd127;
      4'd9:  map_noninv = 7'd111;
      4'd10: map_noninv = 7'd119;
      4'd11: map_noninv = 7'd124;
      4'd12: map_noninv = 7'd57;
      4'd13: map_noninv = 7'd94;
      4'd14: map_noninv = 7'd121;
      default: map_noninv = 7'd113;
    endcase
  endfunction

  function automatic logic [6:0] expected (input logic [3:0] b,
                                           input logic       en,
                                           input logic       pol);
    logic [6:0] sb;
    sb = 7'h00;
    if (en) sb = map_noninv(b);
    if (!pol) sb = ~sb;
    return sb;
  endfunction

  // Core functional equivalence
  assert property (SegOut === expected(ByteIn, Enable, Polarity))
    else $error("FourToSeven mismatch: In=%0d En=%0b Pol=%0b Got=%0h Exp=%0h",
                ByteIn, Enable, Polarity, SegOut, expected(ByteIn,Enable,Polarity));

  // No X/Z on output
  assert property (!$isunknown(SegOut))
    else $error("FourToSeven SegOut has X/Z: %b", SegOut);

  // Enable/polarity corner checks
  assert property (!Enable &&  Polarity |-> SegOut == 7'h00);
  assert property (!Enable && !Polarity |-> SegOut == 7'h7f);

  // Functional coverage: all input/polarity/enable combinations and correct outputs
  genvar i;
  for (i = 0; i < 16; i++) begin : COVS
    cover property ( Enable &&  Polarity && ByteIn == i && SegOut ==  map_noninv(i));
    cover property ( Enable && !Polarity && ByteIn == i && SegOut == ~map_noninv(i));
    cover property (!Enable &&  Polarity && ByteIn == i && SegOut == 7'h00);
    cover property (!Enable && !Polarity && ByteIn == i && SegOut == 7'h7f);
  end

  // Ensure each segment bit toggles both ways at least once
  genvar b;
  for (b = 0; b < 7; b++) begin : TOG
    cover property ($rose(SegOut[b]));
    cover property ($fell(SegOut[b]));
  end

endmodule

bind FourToSeven FourToSeven_sva sva_FourToSeven (
  .ByteIn  (ByteIn),
  .Enable  (Enable),
  .Polarity(Polarity),
  .SegOut  (SegOut)
);