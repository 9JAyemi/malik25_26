
module HilbertTransform (
  input in,
  output out1,
  output out2,
  input clock
);

  parameter N = 32;        // number of filter taps
  parameter Fs = 100;      // sampling frequency

  reg [N-1:0] delay_line; // delay line for filter
  reg [N-1:0] coefficients; // filter coefficients
  reg signed [31:0] real_part; // real part of Hilbert transformed signal
  reg signed [31:0] imag_part; // imaginary part of Hilbert transformed signal

  integer i;

  // initialize filter coefficients
  initial begin
    coefficients = {16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000,
                    16'h0001, 16'h0001, 16'h0001, 16'h0001, 16'h0001, 16'h0001, 16'h0001, 16'h0001,
                    16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000, 16'h0000,
                    16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFF};
  end

  // compute Hilbert transformed signal
  always @(posedge clock) begin
    delay_line[0] <= in;
    real_part <= 0;
    imag_part <= 0;
    for (i = 0; i < N; i = i+2) begin
      real_part <= real_part + delay_line[i]*coefficients[i] - delay_line[i+1]*coefficients[i+1];
      imag_part <= imag_part + delay_line[i]*coefficients[i+1] + delay_line[i+1]*coefficients[i];
    end
    for (i = N-1; i > 0; i = i-1) begin
      delay_line[i] <= delay_line[i-1];
    end
  end

  assign out1 = real_part;
  assign out2 = imag_part;

endmodule
