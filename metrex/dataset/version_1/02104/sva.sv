// SVA for LedDriver
module LedDriver_sva (
  input  logic        clk,
  input  logic [31:0] value,
  input  logic [7:0]  enable,
  input  logic [7:0]  SSEG_CA,
  input  logic [7:0]  SSEG_AN,
  input  logic [2:0]  state,
  input  logic [3:0]  digit,
  input  logic [16:0] timer
);

  default clocking cb @(posedge clk); endclocking

  localparam int unsigned TIMER_MAX = 17'd20000;

  logic started;
  initial started = 1'b0;
  always_ff @(posedge clk) started <= 1'b1;

  function automatic logic [7:0] hex_to_7seg (input logic [3:0] d);
    case (d)
      4'h0: hex_to_7seg = 8'b11000000;
      4'h1: hex_to_7seg = 8'b11111001;
      4'h2: hex_to_7seg = 8'b10100100;
      4'h3: hex_to_7seg = 8'b10110000;
      4'h4: hex_to_7seg = 8'b10011001;
      4'h5: hex_to_7seg = 8'b10010010;
      4'h6: hex_to_7seg = 8'b10000010;
      4'h7: hex_to_7seg = 8'b11111000;
      4'h8: hex_to_7seg = 8'b10000000;
      4'h9: hex_to_7seg = 8'b10010000;
      4'hA: hex_to_7seg = 8'b10001000;
      4'hB: hex_to_7seg = 8'b10000011;
      4'hC: hex_to_7seg = 8'b10100111;
      4'hD: hex_to_7seg = 8'b10100001;
      4'hE: hex_to_7seg = 8'b10000110;
      4'hF: hex_to_7seg = 8'b10001110;
      default: hex_to_7seg = 8'hxx;
    endcase
  endfunction

  // Next-state timing and state machine behavior
  assert property (disable iff (!started)
    timer == (($past(timer) == TIMER_MAX) ? 17'd0 : $past(timer) + 17'd1)
  ) else $error("Timer next-state mismatch");

  assert property (disable iff (!started)
    state == (($past(timer) == TIMER_MAX) ? $past(state) + 3'd1 : $past(state))
  ) else $error("State next-state mismatch");

  // Anode drive mapping (active-low, one-hot or all-off)
  assert property (disable iff (!started)
    ($past(enable[$past(state)])) -> (SSEG_AN == ~(8'b1 << $past(state)))
  ) else $error("SSEG_AN not matching enabled state");

  assert property (disable iff (!started)
    (!$past(enable[$past(state)])) -> (SSEG_AN == 8'hFF)
  ) else $error("SSEG_AN not all-off when disabled");

  assert property (disable iff (!started)
    $onehot0(~SSEG_AN)
  ) else $error("SSEG_AN must be zero- or one-hot low");

  // Digit select and segment decode correctness
  assert property (disable iff (!started)
    digit == $past(value)[$past(state)*4 +: 4]
  ) else $error("Digit select mismatch");

  assert property (disable iff (!started)
    SSEG_CA == hex_to_7seg(digit)
  ) else $error("7-seg decode mismatch");

  // Outputs known after first cycle
  assert property (disable iff (!started)
    !$isunknown({SSEG_AN, SSEG_CA})
  ) else $error("Unknown on outputs");

  // Coverage
  cover property (disable iff (!started) $past(timer)==TIMER_MAX && timer==17'd0);
  cover property (disable iff (!started) $past(state)==3'd7 && $past(timer)==TIMER_MAX && state==3'd0);

  genvar i;
  generate
    for (i=0; i<8; i++) begin : gen_state_cov
      cover property (state==i[2:0]);
      cover property ($past(state)==i[2:0] && $past(enable[i]) && SSEG_AN == ~(8'b1<<i));
      cover property ($past(state)==i[2:0] && !$past(enable[i]) && SSEG_AN == 8'hFF);
    end
  endgenerate

  genvar d;
  generate
    for (d=0; d<16; d++) begin : gen_digit_cov
      cover property (digit == d[3:0] && SSEG_CA == hex_to_7seg(d[3:0]));
    end
  endgenerate

endmodule

// Bind into DUT
bind LedDriver LedDriver_sva sva_inst (
  .clk(clk),
  .value(value),
  .enable(enable),
  .SSEG_CA(SSEG_CA),
  .SSEG_AN(SSEG_AN),
  .state(state),
  .digit(digit),
  .timer(timer)
);