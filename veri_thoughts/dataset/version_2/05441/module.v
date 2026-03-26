
module up_down_counter (
    input CLK, RST, LD, UD,
    input [3:0] LOAD_IN,
    output [3:0] Q
);

reg [3:0] Q;

always @(posedge CLK) begin
    if(RST) begin
        Q <= 4'b0;
    end
    else if(LD) begin
        Q <= LOAD_IN;
    end
    else begin
        if(UD) begin
            Q <= Q + 4'b1;
        end
        else begin
            Q <= Q - 4'b1;
        end
    end
end

endmodule