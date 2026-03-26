module barrel_shifter (
    input [15:0] data,
    input [3:0] shift_amount,
    input direction,
    output reg [15:0] q
);

    always @(*) begin
        if (direction == 1) begin // left shift
            case(shift_amount)
                4'b0000: q = data;
                4'b0001: q = {data[14:0], data[15]};
                4'b0010: q = {data[13:0], data[15:14]};
                4'b0011: q = {data[12:0], data[15:13]};
                4'b0100: q = {data[11:0], data[15:12]};
                4'b0101: q = {data[10:0], data[15:11]};
                4'b0110: q = {data[9:0], data[15:10]};
                4'b0111: q = {data[8:0], data[15:9]};
                4'b1000: q = {data[7:0], data[15:8]};
                4'b1001: q = {data[6:0], data[15:7]};
                4'b1010: q = {data[5:0], data[15:6]};
                4'b1011: q = {data[4:0], data[15:5]};
                4'b1100: q = {data[3:0], data[15:4]};
                4'b1101: q = {data[2:0], data[15:3]};
                4'b1110: q = {data[1:0], data[15:2]};
                4'b1111: q = {data[0], data[15:1]};
            endcase
        end else begin // right shift
            case(shift_amount)
                4'b0000: q = data;
                4'b0001: q = {data[0], data[15:1]};
                4'b0010: q = {data[1:0], data[15:2]};
                4'b0011: q = {data[2:0], data[15:3]};
                4'b0100: q = {data[3:0], data[15:4]};
                4'b0101: q = {data[4:0], data[15:5]};
                4'b0110: q = {data[5:0], data[15:6]};
                4'b0111: q = {data[6:0], data[15:7]};
                4'b1000: q = {data[7:0], data[15:8]};
                4'b1001: q = {data[8:0], data[15:9]};
                4'b1010: q = {data[9:0], data[15:10]};
                4'b1011: q = {data[10:0], data[15:11]};
                4'b1100: q = {data[11:0], data[15:12]};
                4'b1101: q = {data[12:0], data[15:13]};
                4'b1110: q = {data[13:0], data[15:14]};
                4'b1111: q = {data[14:0], data[15]};
            endcase
        end
    end

endmodule