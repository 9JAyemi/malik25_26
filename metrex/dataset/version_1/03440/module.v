
module gray_counter (
    input clk,
    input reset,
    input ena,
    output reg [3:0] q
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 4'b0000;
        end else if (ena) begin
            q <= q ^ (q >> 1);
        end else begin
            q <= q ^ (q << 1);
        end
    end

endmodule
module barrel_shifter (
    input [3:0] a,
    input [1:0] b,
    output [3:0] q
);

    assign q = (b[1]) ? (b[0]) ? {a[1:0], 2'b00} : {2'b00, a[3:2]} : (b[0]) ? {a[0], a[3:1]} : {a[2:0], a[3]};

endmodule
module and_gate (
    input [3:0] a,
    output [3:0] q
);

    assign q = a & 4'b1100;

endmodule
module top_module (
    input clk,
    input reset,
    input ena,
    input [1:0] select, // Fixed the width of 'select' port to 2 bits
    output [3:0] q
);

    wire [3:0] gray_out;
    wire [3:0] shift_out;
    wire [3:0] and_out;

    gray_counter gc (
        .clk(clk),
        .reset(reset),
        .ena(ena),
        .q(gray_out)
    );

    barrel_shifter bs (
        .a(gray_out),
        .b(select),
        .q(shift_out)
    );

    and_gate ag (
        .a(shift_out),
        .q(and_out)
    );

    assign q = and_out;

endmodule