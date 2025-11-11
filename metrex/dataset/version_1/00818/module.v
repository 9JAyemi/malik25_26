
module pipeline_register #(
    parameter width = 8 // width of the data signal
)(
  input wire clk,
  input wire reset,
  input [width-1:0] data_in,
  output reg [width-1:0] data_out
);


always @(posedge clk) begin
    if (reset) begin
        data_out <= 0;
    end else begin
        data_out <= data_in;
    end
end

endmodule
