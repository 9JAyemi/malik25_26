module up_down_counter (
    input clk,
    input reset,
    input up_down,
    output reg [3:0] q
);

    parameter CNT_MAX = 4'b1111;
    parameter CNT_MIN = 4'b0000;

    reg [3:0] cnt_next;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            q <= CNT_MIN;
        end
        else begin
            if (up_down) begin
                cnt_next <= q + 1;
            end
            else begin
                cnt_next <= q - 1;
            end

            if (cnt_next > CNT_MAX) begin
                q <= CNT_MIN;
            end
            else if (cnt_next < CNT_MIN) begin
                q <= CNT_MAX;
            end
            else begin
                q <= cnt_next;
            end
        end
    end

endmodule

module transition_detector (
    input clk,
    input reset,
    input [3:0] q,
    output reg transition
);

    reg [3:0] q_prev;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            q_prev <= 4'b0000;
            transition <= 1'b0;
        end
        else begin
            if (q != q_prev) begin
                transition <= 1'b1;
            end
            else begin
                transition <= 1'b0;
            end
            q_prev <= q;
        end
    end

endmodule

module and_module (
    input transition,
    input [3:0] q,
    output reg [3:0] out
);

    always @(transition or q) begin
        if (transition) begin
            out <= q;
        end
    end

endmodule

module top_module (
    input clk,
    input reset,
    input [31:0] in,
    output [3:0] q
);

    wire transition;
    wire [3:0] cnt_out;

    up_down_counter counter (
        .clk(clk),
        .reset(reset),
        .up_down(in[0]),
        .q(cnt_out)
    );

    transition_detector detector (
        .clk(clk),
        .reset(reset),
        .q(cnt_out),
        .transition(transition)
    );

    and_module and_gate (
        .transition(transition),
        .q(cnt_out),
        .out(q)
    );

endmodule