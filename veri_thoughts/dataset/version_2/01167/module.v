
module shift_register (
    input CLK,
    input LOAD,
    input SHIFT,
    input [7:0] DATA_IN,
    output [7:0] Q_OUT,
    output [7:0] Q_BAR_OUT
);

reg [7:0] shift_reg;

always @(posedge CLK) begin
    if (LOAD) begin
        shift_reg <= DATA_IN;
    end
    else if (SHIFT) begin
        shift_reg <= {shift_reg[6:0], DATA_IN[0]};
    end
end

assign Q_OUT = shift_reg;
assign Q_BAR_OUT = ~shift_reg;

endmodule