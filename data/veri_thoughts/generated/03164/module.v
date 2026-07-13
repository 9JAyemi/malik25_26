module debouncer (
  input clk,
  input in,
  output reg out
);

parameter clk_freq = 100000000;
parameter debounce_time = 50; // in milliseconds

reg [31:0] count;
reg [31:0] debounce_cycles;

always @(posedge clk) begin
  if (in != out) begin
    count <= 0;
    debounce_cycles <= debounce_time * clk_freq / 1000;
  end else if (count < debounce_cycles) begin
    count <= count + 1;
  end else begin
    out <= in;
  end
end

endmodule