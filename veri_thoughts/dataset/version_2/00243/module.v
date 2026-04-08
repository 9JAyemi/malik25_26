module up_down_counter (
    input UD,
    input RST,
    input clk,
    output reg [3:0] Q,
    output reg OVF
);

always @ (posedge clk or negedge RST) begin
    if (RST == 0) begin
        Q <= 4'b0;
        OVF <= 0;
    end
    else if (UD == 1) begin
        if (Q == 4'hF) begin
            Q <= 4'b0;
            OVF <= 1;
        end
        else begin
            Q <= Q + 1;
            OVF <= 0;
        end
    end
    else begin
        if (Q == 4'b0) begin
            Q <= 4'hF;
            OVF <= 1;
        end
        else begin
            Q <= Q - 1;
            OVF <= 0;
        end
    end
end

endmodule