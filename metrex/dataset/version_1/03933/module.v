
module shift_register (
    input CLK,
    input SHIFT,
    input LOAD,
    input [15:0] DATA_IN,
    input mode,
    output [15:0] DATA_OUT
);

    reg [15:0] shift_reg [0:3];
    reg [3:0] shift_cnt;
    wire [15:0] shift_data;

    assign shift_data = (mode) ? 16'hFFFF : 16'h0000;

    always @(posedge CLK) begin
        if (LOAD) begin
            shift_reg[0] <= DATA_IN;
            shift_reg[1] <= shift_data;
            shift_reg[2] <= shift_data;
            shift_reg[3] <= shift_data;
            shift_cnt <= 0;
        end
        else if (SHIFT) begin
            shift_reg[0] <= shift_reg[1];
            shift_reg[1] <= shift_reg[2];
            shift_reg[2] <= shift_reg[3];
            shift_reg[3] <= shift_data;
            shift_cnt <= shift_cnt + 1;
        end
    end

    assign DATA_OUT = shift_reg[shift_cnt];

endmodule