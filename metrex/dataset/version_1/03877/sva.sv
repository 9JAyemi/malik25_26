// SVA for shift_register
// Bind this checker to the DUT instance to verify functionality and coverage.

module shift_register_sva #(
  parameter int n = 4,
  parameter int m = 4,
  parameter int width = 8
)(
  input  logic                 clk,
  input  logic                 reset,
  input  logic                 shift,
  input  logic [n-1:0]         data_in,
  input  logic [m-1:0]         data_out,
  input  logic [width-1:0]     shift_reg
);

  default clocking cb @(posedge clk); endclocking

  // Static/structural checks
  initial begin
    assert (n <= width)
      else $error("SVA: data_in width (n) must be <= shift_reg width");
  end

  // Basic X checks on key controls/inputs
  assert property (cb !$isunknown({reset, shift})));
  assert property (cb !$isunknown(data_in)));

  // Track valid past for $past usage
  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Reset clears next cycle (synchronous reset in RTL)
  assert property (cb reset |=> shift_reg == '0);

  // Load when !shift (with zero-extend if n < width)
  if (n == width) begin
    assert property (cb past_valid && !reset && !shift |=> shift_reg == data_in);
  end else begin
    assert property (cb past_valid && !reset && !shift
                     |=> shift_reg == {{(width-n){1'b0}}, data_in});
  end

  // Right shift when shift==1 (zero into MSB)
  assert property (cb past_valid && !reset && shift
                   |=> shift_reg == {1'b0, $past(shift_reg)[width-1:1]});

  // Output mapping vs internal shift_reg
  if (m == width) begin
    assert property (cb data_out == shift_reg);
  end else if (m < width) begin
    assert property (cb data_out == shift_reg[m-1:0]);
  end else begin // m > width
    assert property (cb data_out[width-1:0] == shift_reg);
    assert property (cb data_out[m-1:width] == '0);
  end

  // Simple covers for key behaviors
  // 1) Reset followed by a load
  cover property (cb reset ##1 !reset && !shift);
  // 2) Load a non-zero then shift once
  cover property (cb !reset && !shift && (data_in != '0) ##1 (!reset && shift));
  // 3) Load a non-zero then shift width times to drain to zero
  cover property (cb !reset && !shift && (data_in != '0)
                      ##1 (!reset && shift) [*width]
                      ##1 shift_reg == '0);

endmodule

// Example bind (adjust instance path as needed)
// bind shift_register shift_register_sva #(.n(n), .m(m), .width(width))
//   u_shift_register_sva (.* , .shift_reg(shift_reg));