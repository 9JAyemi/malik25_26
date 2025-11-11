// SVA bind module for signal_decoder
module signal_decoder_sva #
(
  parameter int ADC_WIDTH = 14,
  parameter int AXIS_TDATA_WIDTH = 32,
  parameter int BIT_OFFSET = 4
)
(
  input  logic                       clk,
  input  logic                       rst,          // active-low synchronous reset
  input  logic [AXIS_TDATA_WIDTH-1:0] S_AXIS_tdata,
  input  logic                       S_AXIS_tvalid, // unused by DUT but kept for bind completeness
  input  logic [7:0]                 led_out,
  input  logic [2:0]                 value          // internal DUT net (bind by name)
);

  // Derived indices
  localparam int HI = ADC_WIDTH - BIT_OFFSET - 1;
  localparam int LO = ADC_WIDTH - BIT_OFFSET - 3;

  // Parameter/index sanity checks (elab-time)
  initial begin
    assert (ADC_WIDTH > BIT_OFFSET + 2)
      else $error("ADC_WIDTH must be > BIT_OFFSET+2");
    assert (HI < AXIS_TDATA_WIDTH)
      else $error("Extract HI index out of S_AXIS_tdata range");
    assert (LO >= 0)
      else $error("Extract LO index out of S_AXIS_tdata range");
    assert (HI >= LO)
      else $error("HI must be >= LO");
  end

  // Expected decode function
  function automatic logic [7:0] expected_led (input logic [2:0] v);
    case (v)
      3'b011: expected_led = 8'b0000_0001;
      3'b010: expected_led = 8'b0000_0010;
      3'b001: expected_led = 8'b0000_0100;
      3'b000: expected_led = 8'b0000_1000;
      3'b111: expected_led = 8'b0001_0000;
      3'b110: expected_led = 8'b0010_0000;
      3'b101: expected_led = 8'b0100_0000;
      3'b100: expected_led = 8'b1000_0000;
      default: expected_led = 8'b0000_0000;
    endcase
  endfunction

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst) // disable during active-low reset

  // Reset behavior (same-cycle check with ##0 to avoid NBA race)
  assert property (@cb (!rst) |-> ##0 (led_out == 8'hFF))
    else $error("led_out not 0xFF during reset");

  // Extracted value must match the intended slice
  assert property (@cb (value == S_AXIS_tdata[HI:LO]))
    else $error("value slice mismatch");

  // No X/Z on used bits in normal operation
  assert property (@cb !$isunknown(value))
    else $error("value has X/Z in normal operation");

  // Functional decode equivalence
  assert property (@cb ##0 (led_out == expected_led(value)))
    else $error("led_out decode mismatch");

  // One-hot check in normal operation (excludes reset)
  assert property (@cb $onehot(led_out))
    else $error("led_out not one-hot");

  // Optional: led_out known (no X/Z) in normal operation
  assert property (@cb !$isunknown(led_out))
    else $error("led_out has X/Z");

  // Coverage: hit all 8 values in normal operation
  cover property (@cb (value == 3'b000));
  cover property (@cb (value == 3'b001));
  cover property (@cb (value == 3'b010));
  cover property (@cb (value == 3'b011));
  cover property (@cb (value == 3'b100));
  cover property (@cb (value == 3'b101));
  cover property (@cb (value == 3'b110));
  cover property (@cb (value == 3'b111));

  // Coverage: exit reset -> valid one-hot decode observed
  cover property (@(posedge clk) (!rst) ##1 (rst && !$isunknown(value)) ##0 $onehot(led_out));

endmodule

// Bind into DUT
bind signal_decoder signal_decoder_sva #(
  .ADC_WIDTH(ADC_WIDTH),
  .AXIS_TDATA_WIDTH(AXIS_TDATA_WIDTH),
  .BIT_OFFSET(BIT_OFFSET)
) u_signal_decoder_sva (
  .clk(clk),
  .rst(rst),
  .S_AXIS_tdata(S_AXIS_tdata),
  .S_AXIS_tvalid(S_AXIS_tvalid),
  .led_out(led_out),
  .value(value)
);