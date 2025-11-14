
module ones_counter (
    input clk,
    input [7:0] in,
    output reg [3:0] count
);

    reg [3:0] temp_count;
    reg [7:0] shift_reg;
    
    always @(posedge clk) begin
        shift_reg <= {shift_reg[6:0], in};
        temp_count <= (shift_reg[7:5] == 3'b111) ? temp_count + 1 : 0;
        count <= temp_count;
    end

endmodule

module triple_counter (
    input clk,
    input [7:0] in,
    input [3:0] ones_count,
    output reg [2:0] triple_count
);

    reg [2:0] temp_count;
    reg [7:0] shift_reg;
    
    always @(posedge clk) begin
        shift_reg <= {shift_reg[6:0], in};
        temp_count <= (shift_reg[7:5] == 3'b111 && ones_count >= 3) ? temp_count + 1 : 0;
        triple_count <= temp_count;
    end

endmodule

module top_module (
    input clk,
    input [7:0] in,
    output [3:0] ones_count,
    output [2:0] triple_count
);

    ones_counter ones_count_inst (
        .clk(clk),
        .in(in),
        .count(ones_count)
    );
    
    triple_counter triple_count_inst (
        .clk(clk),
        .in(in),
        .ones_count(ones_count),
        .triple_count(triple_count)
    );

endmodule

module DFF (
    input clk,
    input reset,
    input d,
    output reg q
);

    always @(posedge clk, posedge reset) begin
        if (reset) begin
            q <= 1'b0;
        end else begin
            q <= d;
        end
    end

endmodule
