module up_down_counter (
    input CLK,
    input LOAD,
    input UP,
    input DOWN,
    output reg [3:0] Q
);

always @(posedge CLK) begin
    if (LOAD) begin
        Q <= 4'b0000;
    end else if (UP) begin
        Q <= (Q == 4'b1111) ? 4'b0000 : Q + 1;
    end else if (DOWN) begin
        Q <= (Q == 4'b0000) ? 4'b1111 : Q - 1;
    end
end

endmodule

module decoder (
    input [1:0] A,
    output reg [15:0] Y
);

always @* begin
    case ({A})
        2'b00: Y = 16'b0000000000000001;
        2'b01: Y = 16'b0000000000000010;
        2'b10: Y = 16'b0000000000000100;
        2'b11: Y = 16'b0000000000001000;
    endcase
end

endmodule

module and_gate (
    input [15:0] Y,
    input [3:0] Q,
    output reg [15:0] AND_output
);

always @* begin
    AND_output = Y & Q;
end

endmodule

module top_module (
    input CLK,
    input LOAD,
    input UP,
    input DOWN,
    output [15:0] Y
);

wire [3:0] Q;
wire [15:0] AND_output;

up_down_counter counter (
    .CLK(CLK),
    .LOAD(LOAD),
    .UP(UP),
    .DOWN(DOWN),
    .Q(Q)
);

decoder decoder (
    .A(Q[1:0]),
    .Y(Y)
);

and_gate and_gate (
    .Y(Y),
    .Q(Q),
    .AND_output(AND_output)
);

endmodule