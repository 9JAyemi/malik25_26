
module mux_4to1 (
    input [7:0] data_in_0,
    input [7:0] data_in_1,
    input [7:0] data_in_2,
    input [7:0] data_in_3,
    input sel1,
    input sel2,
    output reg [7:0] out
);

    always @(*) begin
        case ({sel2, sel1})
            2'b00: out <= data_in_0;
            2'b01: out <= data_in_1;
            2'b10: out <= data_in_2;
            2'b11: out <= data_in_3;
        endcase
    end

endmodule

module shift_left (
    input [7:0] data_in,
    input [3:0] shift,
    output reg [7:0] out
);

    always @(*) begin
        out <= data_in << shift;
    end

endmodule

module adder (
    input [7:0] data_in_1,
    input [7:0] data_in_2,
    output reg [7:0] out
);

    always @(*) begin
        out <= data_in_1 + data_in_2;
    end

endmodule

module shift_mux_adder (
    input [7:0] data_in_0,
    input [7:0] data_in_1,
    input [7:0] data_in_2,
    input [7:0] data_in_3,
    input [3:0] B,
    input sel1,
    input sel2,
    output reg [7:0] out
);

    wire [7:0] mux_out;
    wire [7:0] shift_out;

    mux_4to1 mux_inst (
        .data_in_0(data_in_0),
        .data_in_1(data_in_1),
        .data_in_2(data_in_2),
        .data_in_3(data_in_3),
        .sel1(sel1),
        .sel2(sel2),
        .out(mux_out)
    );

    shift_left shift_inst (
        .data_in(mux_out),
        .shift(B),
        .out(shift_out)
    );

    always @(*) begin
        if (B > 3) begin
            out <= 8'b0;
        end else begin
            out <= shift_out;
        end
    end

endmodule
