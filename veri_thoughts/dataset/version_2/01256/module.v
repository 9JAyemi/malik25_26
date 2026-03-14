
module freq_synthesizer (
  input clk_ref,
  input [31:0] ctrl_word,
  output reg out_clk
);

parameter N = 10;
parameter M = 5;

reg [31:0] counter;
reg [31:0] divider = 0;

always @(posedge clk_ref) begin
  counter <= counter + 1;
  if (counter == N-1) begin
    counter <= 0;
    if (divider == M-1) begin
      divider <= 0;
      out_clk <= ~out_clk;
    end
    else begin
      divider <= divider + 1;
    end
  end
end

endmodule