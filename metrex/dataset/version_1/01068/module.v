module register_4bit (
    input clk,
    input reset,
    input enable,
    input [3:0] data_in,
    output reg [3:0] data_out
);

    always @(posedge clk) begin
        if (reset) begin
            data_out <= 4'b0;
        end else if (enable) begin
            data_out <= data_in;
        end
    end

endmodule