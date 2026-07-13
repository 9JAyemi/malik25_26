
module up_down_counter (
    input clk,
    input load,
    input up_down,
    output reg [2:0] out
);

    always @(posedge clk) begin
        if (load) begin
            out <= 3'b000;
        end
        else if (up_down) begin
            out <= out + 1;
        end
        else begin
            out <= out - 1;
        end
    end

endmodule