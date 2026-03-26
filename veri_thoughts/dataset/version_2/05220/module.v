module up_counter (
    input clk,
    input reset,
    input pause,
    output reg [15:0] q);

    always @(posedge clk) begin
        if (reset) begin
            q <= 16'b0000_0000_0000_0000;
        end else if (!pause) begin
            q <= q + 1;
        end
    end

endmodule

module down_counter (
    input clk,
    input reset,
    input pause,
    output reg [15:0] q);

    always @(posedge clk) begin
        if (reset) begin
            q <= 16'b1111_1111_1111_1111;
        end else if (!pause) begin
            q <= q - 1;
        end
    end

endmodule

module control_logic (
    input up_down,
    input [15:0] up_count,
    input [15:0] down_count,
    output [15:0] q);

    assign q = up_down ? down_count : up_count;

endmodule

module top_module (
    input clk,
    input reset,
    input pause,
    input up_down,
    output [15:0] q);

    reg [15:0] up_count;
    reg [15:0] down_count;

    up_counter up_inst (
        .clk(clk),
        .reset(reset),
        .pause(pause),
        .q(up_count)
    );

    down_counter down_inst (
        .clk(clk),
        .reset(reset),
        .pause(pause),
        .q(down_count)
    );

    control_logic control_inst (
        .up_down(up_down),
        .up_count(up_count),
        .down_count(down_count),
        .q(q)
    );

endmodule