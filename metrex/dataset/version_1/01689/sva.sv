// SVA for shift_register
// Bind with: bind shift_register shift_register_sva sva_i (.*);

module shift_register_sva
(
  input logic       CLK,
  input logic       RST,
  input logic       SHIFT,
  input logic       LOAD,
  input logic [7:0] DATA_IN,
  input logic       DATA_IN_VALID,
  input logic [7:0] DATA_OUT,
  input logic       DATA_OUT_VALID
);

  default clocking cb @(posedge CLK); endclocking

  // Basic X-checks (out of reset)
  assert property (disable iff (RST) !$isunknown({DATA_OUT, DATA_OUT_VALID}));

  // Reset effects
  assert property (RST |-> (DATA_OUT_VALID == 1'b0));
  assert property (RST |=> (DATA_OUT == 8'b0));

  // DATA_OUT behavior (registered mirror of internal shift_reg)
  // Idle holds output
  assert property (disable iff (RST)
                   (!LOAD && !SHIFT) |=> (DATA_OUT == $past(DATA_OUT)));

  // LOAD drives next-cycle DATA_OUT with current DATA_IN
  assert property (disable iff (RST)
                   LOAD |=> (DATA_OUT == $past(DATA_IN)));

  // SHIFT rotates left by 1; appears on DATA_OUT next cycle
  assert property (disable iff (RST)
                   (!LOAD && SHIFT) |=> (DATA_OUT == { $past(DATA_OUT)[6:0], $past(DATA_OUT)[7] }));

  // LOAD has priority over SHIFT (data path)
  assert property (disable iff (RST)
                   (LOAD && SHIFT) |=> (DATA_OUT == $past(DATA_IN)));

  // DATA_OUT_VALID behavior
  // LOAD: mirrors DATA_IN_VALID
  assert property (disable iff (RST)
                   LOAD |-> (DATA_OUT_VALID == DATA_IN_VALID));

  // Not LOAD: always 1 (covers SHIFT and idle)
  assert property (disable iff (RST)
                   (!LOAD) |-> (DATA_OUT_VALID == 1'b1));

  // Functional coverage
  // Observe LOAD -> next DATA_OUT equals DATA_IN
  cover property (disable iff (RST)
                  LOAD |=> (DATA_OUT == $past(DATA_IN)));

  // Observe SHIFT -> next DATA_OUT equals rotated current DATA_OUT
  cover property (disable iff (RST)
                  (!LOAD && SHIFT) |=> (DATA_OUT == { $past(DATA_OUT)[6:0], $past(DATA_OUT)[7] }));

  // LOAD and SHIFT high together (LOAD priority)
  cover property (disable iff (RST)
                  (LOAD && SHIFT));

  // 8 consecutive SHIFTs (no LOAD) return DATA_OUT to original
  cover property (disable iff (RST)
                  (!LOAD && SHIFT)[*8] ##1 (DATA_OUT == $past(DATA_OUT,8)));

endmodule