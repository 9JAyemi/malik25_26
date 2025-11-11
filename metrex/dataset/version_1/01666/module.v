module barrel_shifter (
    input [3:0] data,
    input [1:0] shift,
    output reg [3:0] result
);

    always @(*) begin
        case(shift)
            2'b00: result = data; // no shift
            2'b01: result = {data[2:0], data[3]}; // right shift
            2'b10: result = {data[3], data[2:0]}; // left shift
            2'b11: result = {data[0], data[3:1]}; // rotate left
        endcase
    end

endmodule