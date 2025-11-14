module RC_Oscillator (
  output reg out,
  input clk
);

parameter real r = 100; // value of the resistor in ohms
parameter real c = 1e-6; // value of the capacitor in farads
parameter real f = 1000; // desired frequency of the output waveform in Hz

reg [31:0] count = 0; // counter for generating the waveform
reg state = 0; // state variable for the oscillator

always @ (posedge clk) begin
  if (count == 0) begin
    state <= ~state; // toggle the state variable
  end
  count <= count + 1; // increment the counter
end

always @ (*) begin
  out <= state; // output the state variable as the waveform
end

endmodule