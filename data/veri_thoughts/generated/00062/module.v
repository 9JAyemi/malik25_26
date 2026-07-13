
module shift_mux (
    input [3:0] data_in,
    input [3:0] in_0,
    input [3:0] in_1,
    input [3:0] in_2,
    input [3:0] in_3,
    input [1:0] sel,
    input shift,
    output reg [3:0] out
);

reg [3:0] shift_reg;

always @ (posedge shift) begin
    shift_reg <= {shift_reg[2:0], data_in[3]};
end

always @ (*) begin
    case (sel)
        2'b00: out <= in_0;
        2'b01: out <= in_1;
        2'b10: out <= in_2;
        2'b11: out <= in_3;
        default: out <= shift_reg;
    endcase
end

endmodule