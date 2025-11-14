module glitch_filter #(
  parameter n = 8, // number of bits in the input signal
  parameter t = 2 // duration of the glitch (in clock cycles)
) (
  input wire clk,
  input wire reset,
  input wire [n-1:0] sig_in,
  output wire [n-1:0] sig_out
);

reg [n-1:0] delay_line [0:t-1];
reg [n-1:0] sig_out_reg;
integer i;

always @(posedge clk or posedge reset) begin
  if (reset) begin
    for (i = 0; i < t; i = i + 1) begin
      delay_line[i] <= 0;
    end
    sig_out_reg <= 0;
  end else begin
    for (i = t - 1; i > 0; i = i - 1) begin
      delay_line[i] <= delay_line[i - 1];
    end
    delay_line[0] <= sig_in;

    if (sig_in == delay_line[t - 1]) begin
      sig_out_reg <= sig_in;
    end
  end
end

assign sig_out = sig_out_reg;

endmodule