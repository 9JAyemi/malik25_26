module barrel_shifter (
    input [3:0] data_in,
    input [1:0] shift_amount,
    input mode,
    output reg [3:0] data_out
);

    always @(*) begin
        case (mode)
            2'b00: data_out = data_in << shift_amount; // left shift
            2'b01: data_out = data_in >> shift_amount; // right shift
            2'b10: data_out = {data_in[3], data_in[2:0]}; // rotate left
            2'b11: data_out = {data_in[1:0], data_in[3:2]}; // rotate right
        endcase
    end

endmodule