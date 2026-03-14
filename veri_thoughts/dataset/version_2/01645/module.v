
module up_counter_with_reset_and_load (
    input clk,
    input reset,
    input load,
    output reg [7:0] count
);

    always @(posedge clk) begin
        if (reset) begin
            count <= 0;
        end
        else if (load) begin
            count <= 8'd0;
        end
        else begin
            count <= count + 1;
        end
    end

endmodule
module up_down_counter_with_load (
    input clk,
    input load,
    input up_down,
    output reg [7:0] count
);

    always @(posedge clk) begin
        if (load) begin
            count <= 8'd0;
        end
        else if (up_down) begin
            count <= count + 1;
        end
        else begin
            count <= count - 1;
        end
    end

endmodule
module summing_module (
    input [7:0] count1,
    input [7:0] count2,
    output reg [7:0] sum
);

    always @(count1 or count2) begin
        sum <= count1 + count2;
    end

endmodule
module top_module (
    input clk,
    input reset,
    input load,
    input up_down,
    input [3:0] data_in,
    output [7:0] data_out
);

    reg [7:0] count1;
    reg [7:0] count2;
    wire [7:0] sum;

    up_counter_with_reset_and_load up_counter (
        .clk(clk),
        .reset(reset),
        .load(load),
        .count(count1)
    );

    up_down_counter_with_load up_down_counter (
        .clk(clk),
        .load(load),
        .up_down(up_down),
        .count(count2)
    );

    summing_module summing (
        .count1(count1),
        .count2(count2),
        .sum(sum)
    );

    assign data_out = sum;

endmodule