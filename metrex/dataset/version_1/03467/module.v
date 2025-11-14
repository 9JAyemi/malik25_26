module top_module (
    input [3:0] D,
    input SEL,
    input clk,
    output reg [3:0] OUT
);

    wire [3:0] Y;
    wire [3:0] C;
    wire [3:0] ADD_OUT;

    decoder_2to4_with_enable decoder (
        .D(SEL),
        .E(D[3]),
        .Y(Y)
    );

    twos_comp_converter twos_comp (
        .D(D),
        .C(C)
    );

    adder_4bit adder (
        .A(Y),
        .B(C),
        .CIN(1'b0),
        .S(ADD_OUT)
    );

    always @(posedge clk) begin
        if (SEL == 0) begin
            OUT <= Y[D[1:0]];
        end else begin
            OUT <= ADD_OUT;
        end
    end

endmodule

module decoder_2to4_with_enable (
    input D,
    input E,
    output reg [3:0] Y
);

    always @* begin
        case ({E, D})
            2'b00: Y = 4'b0001;
            2'b01: Y = 4'b0010;
            2'b10: Y = 4'b0100;
            2'b11: Y = 4'b1000;
            default: Y = 4'b0000;
        endcase
    end

endmodule

module twos_comp_converter (
    input [3:0] D,
    output reg [3:0] C
);

    always @* begin
        C = ~D + 4'b1;
    end

endmodule

module adder_4bit (
    input [3:0] A,
    input [3:0] B,
    input CIN,
    output reg [3:0] S
);

    always @* begin
        S = A + B + CIN;
    end

endmodule