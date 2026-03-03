// SVA for hexdisp/hexdigit7seg
// Focused, concise checks + coverage. No DUT changes required.

package hexdisp_sva_pkg;
  function automatic logic [6:0] seg7_low(input logic [3:0] n);
    case (n)
      4'h0: seg7_low = ~7'b1111110;
      4'h1: seg7_low = ~7'b0110000;
      4'h2: seg7_low = ~7'b1101101;
      4'h3: seg7_low = ~7'b1111001;
      4'h4: seg7_low = ~7'b0110011;
      4'h5: seg7_low = ~7'b1011011;
      4'h6: seg7_low = ~7'b1011111;
      4'h7: seg7_low = ~7'b1110000;
      4'h8: seg7_low = ~7'b1111111;
      4'h9: seg7_low = ~7'b1111011;
      4'hA: seg7_low = ~7'b1110111;
      4'hB: seg7_low = ~7'b0011111;
      4'hC: seg7_low = ~7'b1001110;
      4'hD: seg7_low = ~7'b0111101;
      4'hE: seg7_low = ~7'b1001111;
      4'hF: seg7_low = ~7'b1000111;
    endcase
  endfunction
endpackage

// Bind into the leaf: functional truth table, active-low complement, and X-checks
module hexdigit7seg_sva (
  input  logic [3:0] nibble,
  input  logic [6:0] sseg,
  input  logic [6:0] segment
);
  import hexdisp_sva_pkg::*;
  event comb_ev; always @(*) -> comb_ev;
  default clocking cb @ (comb_ev); endclocking

  // Active-low output matches internal active-high register
  assert property (sseg == ~segment);

  // No X/Z on outputs; if input known, output must be known
  assert property (!$isunknown(sseg));
  assert property ((!$isunknown(nibble)) |-> (!$isunknown(sseg)));

  // Exact 16-entry truth table
  assert property ((nibble == 4'h0) |-> (sseg == ~7'b1111110));
  assert property ((nibble == 4'h1) |-> (sseg == ~7'b0110000));
  assert property ((nibble == 4'h2) |-> (sseg == ~7'b1101101));
  assert property ((nibble == 4'h3) |-> (sseg == ~7'b1111001));
  assert property ((nibble == 4'h4) |-> (sseg == ~7'b0110011));
  assert property ((nibble == 4'h5) |-> (sseg == ~7'b1011011));
  assert property ((nibble == 4'h6) |-> (sseg == ~7'b1011111));
  assert property ((nibble == 4'h7) |-> (sseg == ~7'b1110000));
  assert property ((nibble == 4'h8) |-> (sseg == ~7'b1111111));
  assert property ((nibble == 4'h9) |-> (sseg == ~7'b1111011));
  assert property ((nibble == 4'hA) |-> (sseg == ~7'b1110111));
  assert property ((nibble == 4'hB) |-> (sseg == ~7'b0011111));
  assert property ((nibble == 4'hC) |-> (sseg == ~7'b1001110));
  assert property ((nibble == 4'hD) |-> (sseg == ~7'b0111101));
  assert property ((nibble == 4'hE) |-> (sseg == ~7'b1001111));
  assert property ((nibble == 4'hF) |-> (sseg == ~7'b1000111));

  // Coverage: all inputs and corresponding outputs observed
  genvar v;
  for (v = 0; v < 16; v++) begin : C_NIB
    cover property ( (nibble == v[3:0]) and (sseg == seg7_low(v[3:0])) );
  end
endmodule

// Bind into the top: checks correct slicing/ordering across all digits
module hexdisp_sva #(
  parameter int HEX_DIGITS = 8,
  parameter int SEGS_PER_DIGIT = 7
)(
  input  logic [(HEX_DIGITS*4-1):0]                   inword,
  input  logic [(HEX_DIGITS*SEGS_PER_DIGIT-1):0]      outword
);
  import hexdisp_sva_pkg::*;
  event comb_ev; always @(*) -> comb_ev;
  default clocking cb @ (comb_ev); endclocking

  // No X/Z on top-level busses
  assert property (!$isunknown(inword));
  assert property (!$isunknown(outword));

  // Per-digit functional equivalence to golden mapping (catches wiring/slice/order issues)
  genvar i;
  for (i = 0; i < HEX_DIGITS; i++) begin : A_MAP
    localparam int HI = (SEGS_PER_DIGIT*i + SEGS_PER_DIGIT - 1);
    localparam int LO = (SEGS_PER_DIGIT*i);
    assert property (
      outword[HI:LO] == seg7_low(inword[(4*i+3):(4*i)])
    );

    // Coverage: see every hex value on every digit with correct output
    genvar v;
    for (v = 0; v < 16; v++) begin : C_DIG_VAL
      cover property (
        (inword[(4*i+3):(4*i)] == v[3:0]) and
        (outword[HI:LO] == seg7_low(v[3:0]))
      );
    end
  end
endmodule

// Bind statements
bind hexdigit7seg hexdigit7seg_sva u_hexdigit7seg_sva (.nibble(nibble), .sseg(sseg), .segment(segment));
bind hexdisp      hexdisp_sva      #(.HEX_DIGITS(HEX_DIGITS), .SEGS_PER_DIGIT(SEGS_PER_DIGIT))
                                   u_hexdisp_sva (.inword(inword), .outword(outword));