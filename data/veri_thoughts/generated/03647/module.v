module barrel_shifter (
    input [3:0] in,
    input [1:0] shift_amt,
    output reg [3:0] out
);

    always @(*) begin
        case(shift_amt)
            2'b00: out = in;
            2'b01: out = {in[3], in[0], in[1], in[2]};
            2'b10: out = {in[2], in[3], in[0], in[1]};
            2'b11: out = {in[1], in[2], in[3], in[0]};
        endcase
    end

endmodule