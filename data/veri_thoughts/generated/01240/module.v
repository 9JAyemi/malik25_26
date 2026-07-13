module pipelined_counter (
    input clk,
    input reset,      // Asynchronous active-high reset
    output reg [3:0] q);

    reg [3:0] q1, q2, q3;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            q1 <= 4'b0000;
            q2 <= 4'b0000;
            q3 <= 4'b0000;
            q <= 4'b0000;
        end else begin
            q1 <= q;
            q2 <= q1;
            q3 <= q2;
            q <= (q3 == 4'b1111) ? 4'b0000 : q3 + 1;
        end
    end

endmodule

module top_module (
    input clk,
    input reset,      // Asynchronous active-high reset
    output [3:0] q);

    pipelined_counter counter (
        .clk(clk),
        .reset(reset),
        .q(q)
    );

endmodule