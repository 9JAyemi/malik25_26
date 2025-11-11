
module t_ff (
    input clk,
    input t,
    output reg q
);

reg d1, d2;

always @(posedge clk) begin
    d1 <= t;
    d2 <= d1;
    q <= d1 ^ d2;
end

endmodule
module bcd_counter (
    input clk,
    input reset,
    input [2:0] ena, // ena[3] is undef
    output reg [3:0] count
);

always @(posedge clk) begin
    if (reset) begin
        count <= 4'b0000;
    end else begin
        if (ena[0]) begin
            if (count[0] == 4'b1001) begin
                count[0] <= 4'b0000;
                if (ena[1]) begin
                    if (count[1] == 4'b1001) begin
                        count[1] <= 4'b0000;
                        if (ena[2]) begin
                            if (count[2] == 4'b1001) begin
                                count[2] <= 4'b0000;
                                if (count[3] == 4'b1001) begin
                                    count[3] <= 4'b0000;
                                end else begin
                                    count[3] <= count[3] + 1;
                                end
                            end else begin
                                count[2] <= count[2] + 1;
                            end
                        end
                    end else begin
                        count[1] <= count[1] + 1;
                    end
                end
            end else begin
                count[0] <= count[0] + 1;
            end
        end
    end
end

endmodule
module functional_module (
    input t,
    input [3:0] count,
    output [15:0] q
);

assign q = {count, 1'b0} | (t ? 16'b0000000000000001 : 16'b0);

endmodule
module top_module (
    input clk,
    input reset,
    input t,
    output reg [2:0] ena,
    output [15:0] q
);

wire t_ff_q;
wire [3:0] bcd_count;

t_ff t_ff_inst (
    .clk(clk),
    .t(t),
    .q(t_ff_q)
);

bcd_counter bcd_counter_inst (
    .clk(clk),
    .reset(reset),
    .ena(ena),
    .count(bcd_count)
);

functional_module functional_module_inst (
    .t(t_ff_q),
    .count(bcd_count),
    .q(q)
);

initial begin
    ena = 3'b000;
end

endmodule