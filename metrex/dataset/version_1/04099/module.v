
module top_module (
    input [2:0] sel,
    input [5:0] data_in,
    input in,
    output [3:0] mux_out,
    output out,
    output [3:0] or_out
);

    // 6-to-1 Multiplexer
    wire [5:0] mux_input;
    assign mux_input = {data_in[sel], data_in[sel+1], data_in[sel+2], data_in[sel+3], data_in[sel+4], data_in[sel+5]};
    mux_6to1 mux_inst (
        .sel(sel),
        .data_in(mux_input),
        .data_out(mux_out)
    );

    // NOT Gate
    wire not_input;
    assign not_input = in;
    not_gate not_inst (
        .in(not_input),
        .out(out)
    );

    // Bitwise OR
    assign or_out = mux_out | out;

endmodule
module mux_6to1 (
    input [2:0] sel,
    input [5:0] data_in,
    output reg [3:0] data_out
);
    always @*
    begin
        case(sel)
            3'b000: data_out = data_in[0];
            3'b001: data_out = data_in[1];
            3'b010: data_out = data_in[2];
            3'b011: data_out = data_in[3];
            3'b100: data_out = data_in[4];
            3'b101: data_out = data_in[5];
            default: data_out = 4'b0000;
        endcase
    end
endmodule
module not_gate (
    input in,
    output out
);
    wire nand_out;
    assign nand_out = ~(in & in);
    assign out = nand_out;
endmodule