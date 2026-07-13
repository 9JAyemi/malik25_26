
module multiplier (
    input [7:0] a,
    input [7:0] b,
    output reg [15:0] out
);
    always @* begin
        out = a * b;
    end
endmodule

module parity (
    input [7:0] in,
    output reg parity_out
);
    always @* begin
        parity_out = ^in;
    end
endmodule

module additional (
    input [15:0] mult_out,
    input parity_out,
    output reg [15:0] out
);
    always @* begin
        if (parity_out == 1'b0) begin
            out = mult_out + {8'b0, 1'b1};
        end else begin
            out = mult_out;
        end
    end
endmodule

module top_module (
    input [7:0] a,
    input [7:0] b,
    input [7:0] in,
    input select,
    output [15:0] out
);
    wire [15:0] mult_out;
    wire parity_out;
    wire [15:0] add_out;

    multiplier mult_inst (
        .a(a),
        .b(b),
        .out(mult_out)
    );

    parity parity_inst (
        .in(in),
        .parity_out(parity_out)
    );

    additional add_inst (
        .mult_out(mult_out),
        .parity_out(parity_out),
        .out(add_out)
    );

    assign out = select ? add_out : mult_out;
endmodule
