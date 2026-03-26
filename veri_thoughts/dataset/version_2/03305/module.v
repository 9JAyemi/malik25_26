
module top_module(
    input [3:0] data,
    input in,
    output reg out
);

    wire [5:0] mux_input;
    wire not_in;

    not_gate not_gate_inst(
        .in(in),
        .out(not_in)
    );

    mux_6to1 mux_inst(
        .data_in(mux_input),
        .sel({2'b0, not_in}),
        .out(out)
    );

    assign mux_input = {2'b0, data};

endmodule
module mux_6to1(
    input [5:0] data_in,
    input [2:0] sel,
    output reg out
);

    always @(*) begin
        case(sel)
            3'b000: out = data_in[0];
            3'b001: out = data_in[1];
            3'b010: out = data_in[2];
            3'b011: out = data_in[3];
            3'b100: out = data_in[4];
            3'b101: out = data_in[5];
            default: out = 1'b0;
        endcase
    end

endmodule
module not_gate(
    input in,
    output reg out
);

    always @(in) begin
        out = ~in;
    end

endmodule