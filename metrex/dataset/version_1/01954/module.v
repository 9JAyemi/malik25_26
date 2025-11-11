
module up_down_counter (
    input CLK,
    input RST,
    input DIR,
    output reg [15:0] Q
);

    always @(posedge CLK) begin
        if (RST) begin
            Q <= 16'h0000;
        end else begin
            if (DIR) begin
                Q <= Q + 16'b1;
            end else if (Q != 16'h0000) begin
                Q <= Q - 16'b1;
            end
        end
    end

endmodule
module comparator (
    input [15:0] a,
    input [15:0] b,
    output reg lt,
    output reg eq,
    output reg gt
);

    always @(*) begin
        if (a < b) begin
            lt = 1'b1;
            eq = 1'b0;
            gt = 1'b0;
        end else if (a == b) begin
            lt = 1'b0;
            eq = 1'b1;
            gt = 1'b0;
        end else begin
            lt = 1'b0;
            eq = 1'b0;
            gt = 1'b1;
        end
    end

endmodule
module max_value (
    input [15:0] a,
    input lt,
    input eq,
    input gt,
    input [15:0] b,
    output reg [15:0] max_output
);

    always @(*) begin
        if (gt) begin
            max_output = b;
        end else begin
            max_output = a;
        end
    end

endmodule
module top_module (
    input CLK,
    input RST,
    input DIR,
    input [15:0] a,
    input [15:0] b,
    output reg [15:0] Q,
    output reg lt,
    output reg eq,
    output reg gt,
    output reg [15:0] max_output
);

    up_down_counter counter (
        .CLK(CLK),
        .RST(RST),
        .DIR(DIR),
        .Q(Q)
    );

    comparator comp (
        .a(Q),
        .b(b),
        .lt(lt),
        .eq(eq),
        .gt(gt)
    );

    max_value max (
        .a(Q),
        .lt(lt),
        .eq(eq),
        .gt(gt),
        .b(b),
        .max_output(max_output)
    );

endmodule