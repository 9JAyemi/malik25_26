module inverter (
  input signal,
  output reg inverted_signal
);
  
  always @(signal) begin
    inverted_signal <= ~signal;
  end
  
endmodule
