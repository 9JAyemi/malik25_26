module dffe (
    input clk,
    input reset,
    input enable,
    input [31:0] data_in,
    output reg [31:0] data_out
);

always @(posedge clk) begin
    if (reset) begin
        data_out <= 0;
    end else if (enable) begin
        data_out <= data_in;
    end
end

endmodule

module top_module (
    input clk,
    input reset,
    input enable,
    input [31:0] data_in,
    output reg [31:0] data_out
);

dffe dff (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .data_in(data_in),
    .data_out(data_out)
);

endmodule