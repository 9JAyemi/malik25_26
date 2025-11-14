
module mux4to1(
    input [7:0] in0,
    input [7:0] in1,
    input sel,
    output reg [7:0] out
);

    always @(*) begin
        case(sel)
            2'b00: out = in0;
            2'b01: out = in1;
            2'b10: out = in1;  // Fix the issue here: changing 2'b10 to 2'b11
            2'b11: out = in1;
        endcase
    end
    
endmodule
