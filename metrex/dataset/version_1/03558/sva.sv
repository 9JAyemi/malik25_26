// SVA for shift_reg
// Quality-focused, concise checks and coverage

`ifndef SYNTHESIS
module shift_reg_sva #(
  parameter int WIDTH = 4
) (
  input  logic                 clk,
  input  logic                 rst,
  input  logic                 serial_in,
  input  logic                 parallel_in,
  input  logic                 serial_out,
  input  logic [WIDTH-1:0]     reg_data
);

  // Parameter/legal slices
  initial assert (WIDTH >= 2) else $error("WIDTH must be >= 2 for slice ranges used.");

  // Basic sanity: no X on controls, data not X once out of reset
  assert property (@(posedge clk) !$isunknown({rst, parallel_in, serial_in}));
  assert property (@(posedge clk) disable iff (rst) !$isunknown({reg_data, serial_out}));

  // Reset behavior: next cycle clears to zero
  assert property (@(posedge clk) rst |=> reg_data == '0);

  // Combinational tie-off: serial_out reflects MSB
  assert property (@(posedge clk) serial_out == reg_data[WIDTH-1]);

  // Shift/update behavior (matches DUT RTL exactly)
  default clocking @(posedge clk); endclocking
  default disable iff (rst);

  // parallel_in == 1: load MSB from serial_in; lower bits unchanged (per RTL)
  assert property ( parallel_in |=> reg_data == {$past(serial_in), $past(reg_data[WIDTH-2:0])} );

  // parallel_in == 0: left shift; LSB from serial_in
  assert property ( !parallel_in |=> reg_data == {$past(reg_data[WIDTH-2:0]), $past(serial_in)} );

  // Coverage
  cover property (@(posedge clk) rst |=> reg_data == '0);
  cover property ( parallel_in |=> reg_data == {$past(serial_in), $past(reg_data[WIDTH-2:0])} );
  cover property ( !parallel_in |=> reg_data == {$past(reg_data[WIDTH-2:0]), $past(serial_in)} );
  cover property ( !parallel_in ##1 parallel_in ); // mode switch L->R
  cover property ( parallel_in ##1 !parallel_in ); // mode switch R->L
  cover property (@(posedge clk) $rose(serial_out));
  cover property (@(posedge clk) $fell(serial_out));

endmodule

// Bind into DUT
bind shift_reg shift_reg_sva #(.WIDTH(WIDTH)) shift_reg_sva_i (
  .clk(clk),
  .rst(rst),
  .serial_in(serial_in),
  .parallel_in(parallel_in),
  .serial_out(serial_out),
  .reg_data(reg_data)
);
`endif