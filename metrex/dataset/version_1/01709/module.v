module glitch_filter (
  input in,
  input clk, // Added clock input
  output out
);

parameter glitch_duration = 10; // duration of glitch to be removed (in clock cycles)

reg [glitch_duration-1:0] glitch_counter; // counter to measure duration of glitch
reg out_reg; // register to store output signal

always @(posedge clk) begin // Fix: Remove posedge in from the always statement
  if (in == 1'b1) begin
    if (glitch_counter < glitch_duration) begin
      glitch_counter <= glitch_counter + 1;
    end else begin
      out_reg <= 1'b1;
      glitch_counter <= 0;
    end
  end else begin
    if (glitch_counter > 0) begin
      glitch_counter <= glitch_counter - 1;
    end else begin
      out_reg <= 1'b0;
    end
  end
end

assign out = out_reg;

endmodule