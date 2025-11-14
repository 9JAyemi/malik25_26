// SVA for shift_register_32bit
// Uses SHIFT as the clock, bound to DUT and peeks internal pipeline array.

module shift_register_32bit_sva (
  input  logic        SHIFT,
  input  logic        DATA_IN,
  input  logic        SHIFT_OUT,
  input  logic [31:0] DATA_OUT,
  ref    logic [31:0] pipeline [0:2]
);
  default clocking cb @(posedge SHIFT); endclocking

  logic [6:0] seen;
  initial seen = '0;
  always_ff @(posedge SHIFT) seen <= seen + 1'b1;

  // Combinational ties (structural)
  assert property (DATA_OUT == pipeline[2]);
  assert property (SHIFT_OUT == pipeline[0][31]);

  // 1-cycle sequential updates
  assert property (disable iff (seen < 1)
                   pipeline[0] == { $past(pipeline[0][30:0]), $past(DATA_IN) });
  assert property (disable iff (seen < 1)
                   pipeline[1] == $past(pipeline[0]));
  assert property (disable iff (seen < 1)
                   pipeline[2] == $past(pipeline[1]));
  assert property (disable iff (seen < 1)
                   SHIFT_OUT == $past(pipeline[0][30]));

  // Multi-cycle relationships
  assert property (disable iff (seen < 2)
                   DATA_OUT == $past(pipeline[0], 2));
  assert property (disable iff (seen < 32)
                   SHIFT_OUT == $past(DATA_IN, 32));

  // X-propagation sanity when history is known
  assert property (disable iff (seen < 32)
                   !$isunknown($past(DATA_IN,32)) |-> !$isunknown(SHIFT_OUT));

  // Coverage
  cover property (seen >= 32 && SHIFT_OUT == 1'b0);
  cover property (seen >= 32 && SHIFT_OUT == 1'b1);
  cover property (seen >= 2  && $changed(DATA_OUT));
  cover property (seen >= 34 && $changed(SHIFT_OUT));
endmodule

bind shift_register_32bit shift_register_32bit_sva
  u_sva (.SHIFT(SHIFT), .DATA_IN(DATA_IN), .SHIFT_OUT(SHIFT_OUT), .DATA_OUT(DATA_OUT), .pipeline(pipeline));