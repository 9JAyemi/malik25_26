module up_down_counter (
    input clk,
    input reset,
    input up_down,
    output reg [7:0] q
);
    always @(posedge clk) begin
        if (reset) begin
            q <= 8'b0;
        end else if (up_down) begin
            q <= q + 1;
        end else begin
            q <= q - 1;
        end
    end
endmodule

module left_rotator (
    input [3:0] D,
    output reg [3:0] q
);
    always @* begin
        q[0] = D[1];
        q[1] = D[2];
        q[2] = D[3];
        q[3] = D[0];
    end
endmodule

module functional_module (
    input [7:0] up_down_out,
    input [3:0] left_rotator_out,
    input select,
    output reg [7:0] q
);
    always @* begin
        if (select) begin
            q <= up_down_out;
        end else begin
            q <= {left_rotator_out, 4'b0};
        end
    end
endmodule

module top_module (
    input clk,
    input reset,
    input up_down,
    input [3:0] D,
    input select,
    output [7:0] q
);
    wire [7:0] up_down_out;
    wire [3:0] left_rotator_out;

    up_down_counter udc (
        .clk(clk),
        .reset(reset),
        .up_down(up_down),
        .q(up_down_out)
    );

    left_rotator lr (
        .D(D),
        .q(left_rotator_out)
    );

    functional_module fm (
        .up_down_out(up_down_out),
        .left_rotator_out(left_rotator_out),
        .select(select),
        .q(q)
    );
endmodule