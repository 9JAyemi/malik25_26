module mux_6to1 (
    input [2:0] sel,
    input [23:0] data_in,
    output reg [3:0] out
);

always @(*) begin
    case (sel)
        3'b000: out = data_in[3:0];
        3'b001: out = data_in[7:4];
        3'b010: out = data_in[11:8];
        3'b011: out = data_in[15:12];
        3'b100: out = data_in[19:16];
        3'b101: out = data_in[23:20];
        default: out = 4'b0000;
    endcase
end

endmodule