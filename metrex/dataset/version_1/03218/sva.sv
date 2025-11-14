// SVA checker for bcd_converter
module bcd_converter_sva (
  input logic [3:0] D,
  input logic [7:0] BCD
);

  // Sample on any change of D
  event d_ev;
  always @(D) -> d_ev;

  // Helpers
  function automatic logic [3:0] tens(input logic [3:0] x);
    tens = (x > 4'd9) ? 4'd1 : 4'd0;
  endfunction
  function automatic logic [3:0] ones(input logic [3:0] x);
    ones = (x > 4'd9) ? (x - 4'd10) : x;
  endfunction

  // Core mapping check: packed BCD = {tens, ones} for any known D
  property p_bcd_map;
    @(d_ev) !$isunknown(D) |-> (BCD[7:4] == tens(D) && BCD[3:0] == ones(D));
  endproperty
  assert property (p_bcd_map)
    else $error("BCD mismatch: D=%0d BCD=%0h exp={%0d,%0d}", D, BCD, tens(D), ones(D));

  // No X/Z on BCD whenever D is known
  property p_no_x_on_bcd;
    @(d_ev) !$isunknown(D) |-> !$isunknown(BCD);
  endproperty
  assert property (p_no_x_on_bcd);

  // BCD nibbles are valid BCD digits whenever D is known
  property p_valid_bcd_digits;
    @(d_ev) !$isunknown(D) |-> (BCD[7:4] inside {4'd0,4'd1} && BCD[3:0] inside {[4'd0:4'd9]});
  endproperty
  assert property (p_valid_bcd_digits);

  // Functional coverage: hit all 16 input values with correct BCD output
  generate
    genvar i;
    for (i = 0; i < 16; i++) begin : GEN_COV
      localparam logic [3:0] I4  = i;
      localparam logic [3:0] TEN = (i >= 10) ? 4'd1 : 4'd0;
      localparam logic [3:0] ONE = (i >= 10) ? logic'(i-10) : logic'(i);
      cover property (@(d_ev) (D == I4) && (BCD == {TEN, ONE}));
    end
  endgenerate

endmodule

// Bind to DUT
bind bcd_converter bcd_converter_sva u_bcd_converter_sva (.D(D), .BCD(BCD));