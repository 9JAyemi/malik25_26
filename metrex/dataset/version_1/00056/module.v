module barrel_shifter_4bit (
    input [3:0] DATA_IN,
    input [1:0] SHIFT,
    output reg [3:0] DATA_OUT
);

    always @(*) begin
        case(SHIFT)
            2'b00: DATA_OUT = DATA_IN;
            2'b01: DATA_OUT = {DATA_IN[3], DATA_IN[2:0]};
            2'b10: DATA_OUT = {DATA_IN[2:0], DATA_IN[3]};
            2'b11: DATA_OUT = {DATA_IN[1:0], DATA_IN[3:2]};
        endcase
    end

endmodule