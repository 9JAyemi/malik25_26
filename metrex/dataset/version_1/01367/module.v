
module binary_to_bcd(clk, reset, in, out1, out2, out3, out4, clear);
    input clk, reset, clear;
    input [7:0] in;
    output reg [3:0] out1, out2, out3, out4;

    reg [23:0] temp;

    always @(posedge clk) begin
        if (reset) begin
            temp <= 0;
            out1 <= 0;
            out2 <= 0;
            out3 <= 0;
            out4 <= 0;
        end
        else begin
            if (clear) begin
                out1 <= 0;
                out2 <= 0;
                out3 <= 0;
                out4 <= 0;
                temp <= 0;
            end
            else begin
                temp <= {temp[19:0], in};
                if (temp >= 24'd10000) begin
                    temp <= temp + 3'd3;
                end
                if (temp >= 24'd100000) begin
                    temp <= temp + 3'd3;
                end
                if (temp >= 24'd1000000) begin
                    temp <= temp + 3'd3;
                end
                if (temp >= 24'd10000000) begin
                    temp <= temp + 3'd3;
                end
                out1 <= temp[3:0];
                out2 <= temp[7:4];
                out3 <= temp[11:8];
                out4 <= temp[15:12];
            end
        end
    end
endmodule