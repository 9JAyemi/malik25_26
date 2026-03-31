module data_storage(
    input clk,
    input reset,
    input [31:0] in_data,
    input in_valid,
    output reg [31:0] out_data,
    output reg out_valid
);

reg [31:0] stored_data;

always @(posedge clk) begin
    if (reset) begin
        stored_data <= 0;
        out_valid <= 0;
    end else if (in_valid) begin
        stored_data <= in_data;
        out_valid <= 1;
    end else begin
        out_valid <= 0;
    end
end

always @* begin
    out_data = stored_data;
end

endmodule