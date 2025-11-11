module delay_one_cycle(
    input data,
    input clk,
    output to_pad
);

reg delayed_data;

always @(posedge clk) begin
    delayed_data <= data;
end

assign to_pad = delayed_data;

endmodule