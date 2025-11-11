module debouncer(clk, signal_in, debounce_time, signal_out);
  input clk;
  input signal_in;
  input [31:0] debounce_time;
  output signal_out;

  reg [31:0] debounce_counter;
  reg signal_out_reg;
  reg signal_in_reg;

  always @(posedge clk) begin
    if (signal_in != signal_in_reg) begin
      debounce_counter <= debounce_time;
      signal_in_reg <= signal_in;
    end else if (debounce_counter > 0) begin
      debounce_counter <= debounce_counter - 1;
    end else begin
      debounce_counter <= debounce_time;
      signal_out_reg <= signal_in;
    end
  end

  assign signal_out = signal_out_reg;

endmodule