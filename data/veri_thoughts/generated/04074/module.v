
module barrel_shift_encoder (
    input [3:0] A,
    input [1:0] shift,
    input enable,
    output [1:0] pos,
    output [3:0] out
);

reg [3:0] shifted_value;

always @(*) begin
    case(shift)
        2'b00: shifted_value = A;
        2'b01: shifted_value = {A[2:0], A[3]};
        2'b10: shifted_value = {A[1:0], A[3:2]};
        2'b11: shifted_value = {A[0], A[3:1]};
    endcase
end

priority_encoder pe(shifted_value, enable, pos);

assign out = shifted_value | (pos != 0);

endmodule

module priority_encoder (
    input [3:0] in,
    input enable,
    output reg [1:0] pos
);

always @(*) begin
    if (enable) begin
        case(in)
            4'b0001: pos = 0;
            4'b0010: pos = 1;
            4'b0100: pos = 2;
            4'b1000: pos = 3;
            default: pos = 0;
        endcase
    end
    else begin
        pos = 0;
    end
end

endmodule

module top_module (
    input [3:0] A,
    input [1:0] shift,
    input [3:0] in,
    input enable,
    output [1:0] pos,
    output [3:0] out
);

barrel_shift_encoder bse(A, shift, enable, pos, out);
    
endmodule
