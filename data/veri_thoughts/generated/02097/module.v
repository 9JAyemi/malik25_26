module barrel_shifter (
    input [3:0] data,
    input [1:0] shift_amount,
    output reg [3:0] result
);

    always @(*) begin
        case(shift_amount)
            2'b00: result = data;
            2'b01: result = {data[3], data[0], data[1], data[2]};
            2'b10: result = {data[2], data[3], data[0], data[1]};
            2'b11: result = {data[1], data[2], data[3], data[0]};
        endcase
    end

endmodule