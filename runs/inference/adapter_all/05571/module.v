
module top_module (
    input clk,
    input reset,
    input [7:0] d1,
    input [7:0] d2,
    output [7:0] q,
    output [7:0] count
);

// instantiate register module
reg_module reg_inst(
    .clk(clk),
    .reset(reset),
    .d(d1 + d2),
    .en(1'b1),
    .q(q)
);

// instantiate counter module
counter_module counter_inst(
    .clk(clk),
    .reset(reset),
    .en(1'b1),
    .count(count)
);

endmodule

module reg_module (
    input clk,
    input reset,
    input [7:0] d,
    input en,
    output reg [7:0] q
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 0;
        end else if (en) begin
            q <= d;
        end
    end

endmodule

module counter_module (
    input clk,
    input reset,
    input en,
    output reg [7:0] count
);

    always @(posedge clk) begin
        if (reset) begin
            count <= 0;
        end else if (en) begin
            count <= count + 1;
        end
    end

endmodule
