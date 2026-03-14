
module up_down_counter (
    input clk,
    input up_down,
    input load,
    output reg [2:0] count
);

    always @(posedge clk) begin
        if (load)
            count <= 3'b000;
        else if (up_down)
            count <= count + 1;
        else
            count <= count - 1;
    end

endmodule

module unsigned_multiplier (
    input [3:0] A,
    input [3:0] B,
    output reg [7:0] P
);

    always @(*) begin
        P = A * B;
    end

endmodule

module top_module (
    input clk,
    input up_down,
    input load,
    input select,
    input [3:0] A,
    input [3:0] B,
    output wire [2:0] count,
    output wire [7:0] P
);

    wire [2:0] count_int;
    wire [7:0] P_int;

    up_down_counter counter(
        .clk(clk),
        .up_down(up_down),
        .load(load),
        .count(count_int)
    );

    unsigned_multiplier multiplier(
        .A(A),
        .B(B),
        .P(P_int)
    );

    assign count = select ? 3'b0 : count_int;
    assign P = select ? 8'b0 : P_int;

endmodule
