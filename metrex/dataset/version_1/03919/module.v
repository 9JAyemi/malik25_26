
module priority_encoder (
    input [7:0] a, b, c, d,
    output [2:0] index);

    wire [7:0] temp;

    assign temp = {a, b, c, d}; 
    assign index = 3'b000; 
endmodule
module min_decade_counter (
    input clk,
    input reset,
    input [7:0] a, b, c, d,
    input clock_enable,
    output [7:0] min,
    output [3:0] q);

    wire [2:0] index;
    priority_encoder pe(.a(a), .b(b), .c(c), .d(d), .index(index));

    reg [3:0] counter = 0;
    always @(posedge clk) begin
        if (reset) begin
            counter <= 0;
        end else if (clock_enable) begin
            counter <= (counter == 9) ? 0 : counter + 1;
        end
    end

    assign min = (index == 3'b000) ? a :
                 (index == 3'b001) ? b :
                 (index == 3'b010) ? c :
                 (index == 3'b011) ? d :
                 8'b0 ;
    assign q = counter;
endmodule
module top_module (
    input clk,
    input reset,
    input [7:0] a, b, c, d,
    input select,
    input clock_enable,
    output [7:0] min,
    output [3:0] q);

    wire [7:0] min_value;
    wire [3:0] counter_value;

    min_decade_counter mdc(.clk(clk), .reset(reset), .a(a), .b(b), .c(c), .d(d), .clock_enable(clock_enable), .min(min_value), .q(counter_value));

    assign min = (select) ? min_value : 8'b0;
    assign q = (select) ? counter_value : 4'b0;
endmodule