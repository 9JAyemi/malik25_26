module binary_counter
#(
    parameter WIDTH = 4
)
(
    input clk,
    input rst,
    input en,
    input load,
    input [WIDTH-1:0] data,
    output [WIDTH-1:0] count,
    output max_flag
);

    reg [WIDTH-1:0] counter;

    assign max_flag = (counter == {WIDTH{1'b1}});

    always @(posedge clk or negedge rst) begin
        if (!rst) begin
            counter <= 0;
        end else if (load) begin
            counter <= data;
        end else if (en) begin
            counter <= counter + 1;
        end
    end

    assign count = counter;

endmodule