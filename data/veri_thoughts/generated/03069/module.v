module up_down_counter (
    input clk,
    input up_down,
    input reset,
    output reg [2:0] count
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            count <= 3'b0;
        end
        else if (up_down) begin
            count <= count + 1;
        end
        else begin
            count <= count - 1;
        end
    end

endmodule