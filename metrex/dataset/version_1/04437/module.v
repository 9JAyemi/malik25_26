module data_out_on_rising_edge (input data_in, clk, output reg data_out);

always @(posedge clk) begin
  data_out <= data_in;
end

endmodule