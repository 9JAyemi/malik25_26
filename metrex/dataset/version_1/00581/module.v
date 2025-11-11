module top_module (
    input [3:0] in0,
    input [3:0] in1,
    input enable,
    output reg [7:0] out
);

    wire [3:0] cmp_out;
    wire [7:0] dec_out;
    
    comparator cmp(.in0(in0), .in1(in1), .out(cmp_out));
    decoder dec(.in(cmp_out), .enable(enable), .out(dec_out));
    
    always @(*) begin
        if (cmp_out == 4'b0000) // in0 = in1
            out = dec_out[0];
        else if (cmp_out > 4'b0000) // in0 > in1
            out = dec_out[1];
        else // in0 < in1
            out = dec_out[2];
    end
    
endmodule

module comparator (
    input [3:0] in0,
    input [3:0] in1,
    output reg [3:0] out
);
    
    always @(*) begin
        if (in0 == in1)
            out = 4'b0000;
        else if (in0 > in1)
            out = 4'b0001;
        else
            out = 4'b0010;
    end
    
endmodule

module decoder (
    input [3:0] in,
    input enable,
    output reg [7:0] out
);
    
    always @(*) begin
        case (in)
            4'b0000: out = 8'b00000001;
            4'b0001: out = 8'b00000010;
            4'b0010: out = 8'b00000100;
            4'b0011: out = 8'b00001000;
            4'b0100: out = 8'b00010000;
            4'b0101: out = 8'b00100000;
            4'b0110: out = 8'b01000000;
            4'b0111: out = 8'b10000000;
            default: out = 8'b00000000;
        endcase
        
        if (!enable)
            out = 8'b00000000;
    end
    
endmodule