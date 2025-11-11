module priority_encoder (
    input [15:0] I,
    input EN,
    output reg [3:0] O
);

reg [3:0] temp;

always @ (posedge EN) begin
    temp <= (I[15:12] > I[11:8]) > (I[7:4] > I[3:0]);
end

always @* begin
    case(temp)
        4'b0001: O = 4'b0001;
        4'b0010: O = 4'b0010;
        4'b0100: O = 4'b0100;
        4'b1000: O = 4'b1000;
        default: O = 4'b0000;
    endcase
end

endmodule