module counter_2bit(
    input clk,
    input rst,
    output reg [1:0] count
);

    always @(posedge clk or negedge rst) begin
        if (!rst) begin
            count <= 2'b00;
        end else begin
            count <= count + 1;
        end
    end

endmodule