
module up_down_counter (
    input clk,
    input reset,
    input [3:0] load,
    input [1:0] mode,
    output reg [3:0] count_out
);

    reg [3:0] count_reg;

    always @(posedge clk) begin
        if (reset) begin
            count_reg <= 4'b0;
        end else begin
            case (mode)
                2'b00: count_reg <= count_reg + 1;
                2'b01: count_reg <= count_reg - 1;
                2'b10: count_reg <= load;
            endcase
        end
    end

    always @(*) begin
        count_out <= count_reg;
    end

endmodule

module comparator (
    input [3:0] a,
    input [3:0] b,
    output reg equal_out
);

    always @(*) begin
        if (a == b) begin
            equal_out <= 1'b1;
        end else begin
            equal_out <= 1'b0;
        end
    end

endmodule

module top_module (
    input clk,
    input reset,
    input [3:0] load,
    input [3:0] compare,
    input [1:0] mode,
    output [3:0] count_out,
    output equal_out
);

    wire [3:0] count_wire;
    wire equal_wire;

    up_down_counter counter_inst (
        .clk(clk),
        .reset(reset),
        .load(load),
        .mode(mode),
        .count_out(count_wire)
    );

    comparator comparator_inst (
        .a(count_wire),
        .b(compare),
        .equal_out(equal_wire)
    );

    assign count_out = count_wire;
    assign equal_out = equal_wire;

endmodule
