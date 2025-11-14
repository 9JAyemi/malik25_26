module POR (
  input vdd, // power supply signal
  input clk, // clock signal
  output reg rst // reset signal
);

  reg [23:0] counter; // 24-bit counter for delay time
  
  always @(posedge clk) begin
    if (vdd == 1'b0) begin // power removed
      rst <= 1'b1; // set reset signal high
      counter <= 0; // reset counter
    end
    else if (counter == 24'd100000) begin // delay time elapsed
      rst <= 1'b0; // set reset signal low
    end
    else begin // count up
      counter <= counter + 1;
    end
  end
  
endmodule