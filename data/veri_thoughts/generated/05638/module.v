module binary_counter(
    input wire clk,
    input wire rst,
    input wire test_mode,
    input wire up,
    input wire down,
    output reg [3:0] count
);

    always @(posedge clk or negedge rst) begin
        if (~rst) begin
            count <= 4'b0;
        end else if (~test_mode) begin
            count <= count + 1;
        end else begin
            if (up) begin
                count <= (count == 4'b1111) ? 4'b0 : count + 1;
            end else if (down) begin
                count <= (count == 4'b0000) ? 4'b1111 : count - 1;
            end
        end
    end

endmodule