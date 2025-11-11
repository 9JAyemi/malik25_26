// SVA for KeyEncoder. Bind this module to the DUT.
module KeyEncoder_sva
(
  input  logic        Clock,
  input  logic        Reset,
  input  logic [3:0]  Columns,
  input  logic [3:0]  Rows,
  input  logic [3:0]  TensDigit,
  input  logic [3:0]  OnesDigit,
  input  logic        Found
);

  // Convenience signals
  logic [7:0] cr;       // {Columns,Rows}
  logic [7:0] td;       // {TensDigit,OnesDigit}
  logic [8:0] out;      // {Found,TensDigit,OnesDigit}
  assign cr  = {Columns,Rows};
  assign td  = {TensDigit,OnesDigit};
  assign out = {Found,TensDigit,OnesDigit};

  // Golden decode function (mirrors DUT case)
  function automatic logic [8:0] decode(input logic [7:0] in);
    unique case (in)
      8'b01110111: decode = 9'b100000001; // 1
      8'b10110111: decode = 9'b100000010; // 2
      8'b11010111: decode = 9'b100000011; // 3
      8'b01111011: decode = 9'b100000100; // 4
      8'b10111011: decode = 9'b100000101; // 5
      8'b11011011: decode = 9'b100000110; // 6
      8'b01111101: decode = 9'b100000111; // 7
      8'b10111101: decode = 9'b100001000; // 8
      8'b11011101: decode = 9'b100001001; // 9
      8'b11100111: decode = 9'b100010000; // A
      8'b11101011: decode = 9'b100010001; // B
      8'b11101101: decode = 9'b100010010; // C
      8'b11101110: decode = 9'b100010011; // D
      8'b01111110: decode = 9'b100010100; // *
      8'b10111110: decode = 9'b100010101; // 0
      8'b11011110: decode = 9'b100010110; // #
      default:     decode = 9'd0;         // NoKey
    endcase
  endfunction

  // Set of valid input patterns (for conciseness reuse)
  localparam logic [7:0] K1  = 8'b01110111;
  localparam logic [7:0] K2  = 8'b10110111;
  localparam logic [7:0] K3  = 8'b11010111;
  localparam logic [7:0] K4  = 8'b01111011;
  localparam logic [7:0] K5  = 8'b10111011;
  localparam logic [7:0] K6  = 8'b11011011;
  localparam logic [7:0] K7  = 8'b01111101;
  localparam logic [7:0] K8  = 8'b10111101;
  localparam logic [7:0] K9  = 8'b11011101;
  localparam logic [7:0] KA  = 8'b11100111;
  localparam logic [7:0] KB  = 8'b11101011;
  localparam logic [7:0] KC  = 8'b11101101;
  localparam logic [7:0] KD  = 8'b11101110;
  localparam logic [7:0] KS  = 8'b01111110; // *
  localparam logic [7:0] K0  = 8'b10111110; // 0
  localparam logic [7:0] KP  = 8'b11011110; // #

  // 1) Decode correctness (core functional check)
  assert property (@(posedge Clock) disable iff (Reset)
    out == decode(cr))
    else $error("KeyEncoder decode mismatch: cr=%b out=%b exp=%b", cr, out, decode(cr));

  // 2) Found equivalence to valid input set
  assert property (@(posedge Clock) disable iff (Reset)
    Found == (cr inside {K1,K2,K3,K4,K5,K6,K7,K8,K9,KA,KB,KC,KD,KS,K0,KP}));

  // 3) Digit legality vs Found
  assert property (@(posedge Clock) disable iff (Reset)
    Found |-> (td inside {[8'h01:8'h09],[8'h10:8'h16]}));
  assert property (@(posedge Clock) disable iff (Reset)
    !Found |-> (td == 8'h00));

  // 4) Default path for any non-key pattern
  assert property (@(posedge Clock) disable iff (Reset)
    !(cr inside {K1,K2,K3,K4,K5,K6,K7,K8,K9,KA,KB,KC,KD,KS,K0,KP}) |-> (out == 9'd0));

  // 5) Reset behavior (async and while asserted)
  assert property (@(posedge Reset) out == 9'd0);
  assert property (@(posedge Clock) Reset |-> out == 9'd0);

  // 6) No X/Z on outputs
  assert property (@(posedge Clock) !$isunknown(out));

  // 7) Optional structural sanity on recognized keys: one-cold per nibble
  assert property (@(posedge Clock) disable iff (Reset)
    Found |-> ((^~Columns) && (^~Rows))); // even parity of inverted -> exactly one 0 for 4b nibbles

  // Coverage: hit each key and default
  cover property (@(posedge Clock) !Reset && cr==K1  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==K2  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==K3  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==K4  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==K5  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==K6  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==K7  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==K8  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==K9  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==KA  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==KB  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==KC  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==KD  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==KS  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==K0  && out==decode(cr));
  cover property (@(posedge Clock) !Reset && cr==KP  && out==decode(cr));
  cover property (@(posedge Clock) !Reset &&
                  !(cr inside {K1,K2,K3,K4,K5,K6,K7,K8,K9,KA,KB,KC,KD,KS,K0,KP}) &&
                  out==9'd0);
  cover property (@(posedge Reset) out==9'd0);

endmodule

// Bind to DUT (instantiate once in your testbench or a bind file)
bind KeyEncoder KeyEncoder_sva sva_i(
  .Clock(Clock),
  .Reset(Reset),
  .Columns(Columns),
  .Rows(Rows),
  .TensDigit(TensDigit),
  .OnesDigit(OnesDigit),
  .Found(Found)
);