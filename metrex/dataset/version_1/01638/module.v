module ParamModule (
    input clk,
    input reset_l,
    input [3:0] param1,
    input [7:0] param2,
    input [15:0] param3,
    output reg [31:0] result
);

    parameter PARAM1 = 2;
    parameter PARAM2 = 4;
    parameter PARAM3 = 8;

    always @(posedge clk) begin
        if (!reset_l) begin
            result <= 0;
        end else begin
            result <= param1 + param2 + param3;
        end
    end

endmodule