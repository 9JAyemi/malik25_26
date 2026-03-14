
module up_down_counter (
    input clk,
    input reset,
    input up_down,
    input load,
    input [3:0] data_in,
    output reg [3:0] count
);

    always @ (posedge clk or posedge reset) begin
        if (reset) begin
            count <= 4'b0000;
        end else if (load) begin
            count <= data_in;
        end else if (up_down) begin
            count <= count + 1;
        end else begin
            count <= count - 1;
        end
    end
endmodule

module top_module (
    input clk,
    input reset,
    input up_down,
    input load,
    input [3:0] data_in,
    output wire [3:0] count,
    output wire [3:0] sum
);
    wire [3:0] up_count, down_count;

    up_down_counter up_counter (
        .clk(clk),
        .reset(reset),
        .up_down(1'b1),
        .load(load),
        .data_in(data_in),
        .count(up_count)
    );

    up_down_counter down_counter (
        .clk(clk),
        .reset(reset),
        .up_down(1'b0),
        .load(load),
        .data_in(data_in),
        .count(down_count)
    );

    assign count = up_down ? up_count : down_count;
    assign sum = up_count + down_count;
endmodule
