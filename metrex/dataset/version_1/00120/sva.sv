// SVA for DALU. Bind this module to the DUT.
// Focuses on FSM correctness, handshake, output validity, stability, and ALU functional checks.

module DALU_sva
(
  input  logic                  clk,
  input  logic                  rst,
  input  logic                  in_valid,
  input  logic [18:0]           instruction,
  input  logic                  out_valid,
  input  logic signed [15:0]    out,
  // internal state from DUT
  input  logic [1:0]            cState
);

  // Mirror DUT params (OP is unused)
  localparam int IDLE   = 0;
  localparam int INPUT  = 1;
  localparam int OUTPUT = 2;

  // Decode (same as DUT)
  logic [2:0]            L;
  logic signed [5:0]     s, t;
  logic signed [3:0]     l;
  logic signed [9:0]     i;

  assign L = instruction[18:16];
  assign s = instruction[15:10];
  assign t = instruction[9:4];
  assign l = instruction[3:0];
  assign i = instruction[9:0];

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Simple 16-bit signed model of DUT operations (matches DUT sizing semantics)
  function automatic signed [15:0] alu_model(
    input logic [2:0]            Lf,
    input logic signed [5:0]     sf, tf,
    input logic signed [3:0]     lf,
    input logic signed [9:0]     if_,
    input signed [15:0]          prev_out
  );
    automatic signed [15:0] s16 = sf;
    automatic signed [15:0] t16 = tf;
    automatic signed [15:0] l16 = lf;
    automatic signed [15:0] i16 = if_;
    automatic signed [15:0] sum = s16 + t16 + l16;
    alu_model = prev_out;
    unique case (Lf)
      3'd0: begin
        unique case (lf[3:0])
          4'd0: alu_model = s16 & t16;
          4'd1: alu_model = s16 | t16;
          4'd2: alu_model = s16 ^ t16;
          4'd3: alu_model = s16 + t16;
          4'd4: alu_model = s16 - t16;
          default: alu_model = prev_out; // no-op as in RTL
        endcase
      end
      3'd1: alu_model = s16 * t16 * l16;               // fits in 16 bits for given ranges
      3'd2: alu_model = (sum) * (sum);                 // (s+t+l)^2, 16-bit
      3'd3: alu_model = s16 + i16;
      3'd4: alu_model = s16 - i16;
      default: alu_model = prev_out;                   // no-op as in RTL
    endcase
  endfunction

  // Handy sequences
  sequence start_ev;
    (cState == IDLE && in_valid);
  endsequence

  sequence full_txn;
    start_ev ##1 (cState == INPUT)
      ##[0:$] (cState == INPUT && !in_valid)
      ##1 (cState == OUTPUT && out_valid)
      ##1 (cState == IDLE && !out_valid);
  endsequence

  // Reset behavior
  assert property (rst |-> (cState == IDLE && out_valid == 1'b0 && out == 16'sd0));

  // State encoding is always legal
  assert property (cState inside {IDLE, INPUT, OUTPUT});

  // FSM transitions (intended spec; catches latch/NS bugs)
  assert property ((cState == IDLE  &&  in_valid) |=> cState == INPUT);
  assert property ((cState == IDLE  && !in_valid) |=> cState == IDLE);
  assert property ((cState == INPUT &&  in_valid) |=> cState == INPUT);
  assert property ((cState == INPUT && !in_valid) |=> cState == OUTPUT);
  assert property ((cState == OUTPUT)              |=> cState == IDLE);

  // out_valid is 1 only in OUTPUT and is a single-cycle pulse
  assert property (out_valid == (cState == OUTPUT));
  assert property (out_valid |=> !out_valid);
  // An out_valid must be preceded by INPUT with in_valid deassert
  assert property (out_valid |-> ($past(cState) == INPUT && !$past(in_valid)));

  // Functional check: on start, next cycle out equals model; otherwise out holds
  assert property (start_ev |=> out == alu_model(L, s, t, l, i, $past(out)));

  // out only changes when capturing (IDLE & in_valid), else it must hold
  assert property (! (cState == IDLE && in_valid) |=> $stable(out));
  // Stronger: out is stable in INPUT and OUTPUT
  assert property ((cState inside {INPUT, OUTPUT}) |=> $stable(out));

  // No X on critical outputs/states after reset
  assert property (!$isunknown({cState, out_valid, out}));

  // Coverage
  cover property (full_txn);
  cover property (start_ev && L == 3'd0 && l == 4'd0); // AND
  cover property (start_ev && L == 3'd0 && l == 4'd1); // OR
  cover property (start_ev && L == 3'd0 && l == 4'd2); // XOR
  cover property (start_ev && L == 3'd0 && l == 4'd3); // ADD
  cover property (start_ev && L == 3'd0 && l == 4'd4); // SUB
  cover property (start_ev && L == 3'd0 && !(l inside {4'd0,4'd1,4'd2,4'd3,4'd4})); // default no-op
  cover property (start_ev && L == 3'd1);             // s*t*l
  cover property (start_ev && L == 3'd2);             // (s+t+l)^2
  cover property (start_ev && L == 3'd3);             // s+i
  cover property (start_ev && L == 3'd4);             // s-i
  cover property (start_ev && L inside {3'd5,3'd6,3'd7}); // default no-op L

endmodule

// Example bind (place in a package or a separate SV file included in sim)
// bind DALU DALU_sva sva (.*, .cState(cState));