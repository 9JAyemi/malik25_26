
module stratixii_lvds_rx_deser #(
    parameter channel_width = 10
)(
    input clk,
    input datain,
    input devclrn,
    input devpor,
    output [channel_width-1:0] dataout
);


reg [channel_width-1:0] shift_reg;

always @(posedge clk) begin
    if (devclrn || devpor) begin
        shift_reg <= 0;
    end else begin
        shift_reg <= {shift_reg[channel_width-2:0], datain};
    end
end

assign dataout = shift_reg;

endmodule
