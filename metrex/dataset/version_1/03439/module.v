module Depulser(
  input   wire clock,
  input   wire reset,
  input   wire io_in,
  input   wire io_rst,
  output  reg  io_out
);
  wire  r_clock;
  wire  r_reset;
  wire  r_io_in;
  wire  r_io_init;
  reg   r_io_out;
  wire  r_io_enable;
  wire  _T_9;
  wire  _T_11;
  
  reg [1:0] state = 2'b00; // Initialize state to 0
  wire pulse;
  
  assign pulse = (r_io_in == 1'b1) && (state == 2'b00); // Detect a pulse
  
  always @(posedge r_clock or posedge r_reset) begin
    if (r_reset == 1'b1) begin // Reset output to 0
      r_io_out <= 1'b0;
      state <= 2'b00;
    end else if (pulse) begin // Hold output high for one clock cycle
      r_io_out <= 1'b1;
      state <= 2'b01;
    end else if (state == 2'b01) begin // Return output to 0
      r_io_out <= 1'b0;
      state <= 2'b10;
    end else begin // Pass input to output
      r_io_out <= r_io_in;
      state <= 2'b00;
    end
  end
  
  always @* begin
    io_out = r_io_out;
  end
  
  assign r_clock = clock;
  assign r_reset = reset;
  assign r_io_in = _T_9;
  assign r_io_init = 1'h0;
  assign r_io_enable = _T_11;
  assign _T_9 = io_rst ? 1'h0 : io_in;
  assign _T_11 = io_in | io_rst;
endmodule