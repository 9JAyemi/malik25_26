module my_module (
    input clk,
    input rst,
    input [31:0] in_data,
    output reg [31:0] out_data
);

    always @(posedge clk) begin
        if (rst) begin
            out_data <= 0;
        end else begin
            out_data <= in_data;
        end
    end

endmodule