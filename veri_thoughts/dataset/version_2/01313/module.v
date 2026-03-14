module decade_counter (
    input clk,
    input reset,
    input pause,
    output reg [3:0] q
);

    parameter COUNT_MAX = 10;
    parameter COUNT_WIDTH = 4;

    reg [COUNT_WIDTH-1:0] count;

    always @(posedge clk) begin
        if (reset) begin
            count <= 0;
        end else if (!pause) begin
            count <= count + 1;
        end
    end

    always @(count) begin
        if (count == COUNT_MAX) begin
            q <= 0;
        end else begin
            q <= count;
        end
    end

endmodule

module top_module (
    input clk,
    input slowena,
    input reset,
    output [3:0] q
);

    wire slow_clk = clk & slowena;
    wire pause = ~slowena;

    decade_counter counter (
        .clk(slow_clk),
        .reset(reset),
        .pause(pause),
        .q(q)
    );

endmodule