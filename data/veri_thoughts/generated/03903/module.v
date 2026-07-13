
module mux3(
    input in0,
    input in1,
    input in2,
    input [1:0] sel,
    input clr,
    input set,
    output reg out
);

always @(*) begin
    if(set) begin
        out <= 1'b1;
    end
    else if(clr) begin
        out <= 1'b0;
    end
    else begin
        case(sel)
            2'b00: out = in0;
            2'b01: out = in1;
            2'b10: out = in2;
            2'b11: out = 1'b0;
        endcase
    end
end

endmodule