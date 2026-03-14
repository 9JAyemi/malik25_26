
module priority_encoder (
    input [7:0] a, b, c, d,
    output reg [1:0] index
);

    always @* begin
        if ({a,b,c,d} != 8'b00000000)
            index = a ? 2'b00 : (b ? 2'b01 : (c ? 2'b10 : 2'b11));
        else
            index = 2'b11;
    end

endmodule
module mux_4to1_priority_encoder (
    input [7:0] a, b, c, d,
    input [1:0] select,
    output reg [7:0] out
);

    wire [1:0] index;
    priority_encoder pe(a, b, c, d, index);

    always @* begin
        case (select)
            2'b00: out = a;
            2'b01: out = b;
            2'b10: out = c;
            2'b11: out = d;
        endcase
    end

endmodule