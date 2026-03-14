
module top_module (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    output reg [7:0] q
);

    wire greater_than;
    wire equal;
    wire enable;
    wire [3:0] count;
    wire [7:0] sum;

    // Instantiate the 8-bit comparator module
    comparator_module comparator_inst(
        .a(a),
        .b(b),
        .greater_than(greater_than)
    );
    
    // Instantiate the 4-bit binary counter module
    counter_module counter_inst(
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .count(count)
    );
    
    // Instantiate the control logic module
    control_logic_module control_inst(
        .a(a),
        .b(b),
        .greater_than(greater_than),
        .equal(equal),
        .enable(enable)
    );
    
    // Instantiate the additional functional module
    functional_module functional_inst(
        .a(a[0]),
        .b(count),
        .sum(sum)
    );
    
    // Output the appropriate value based on the control logic
    always @(posedge clk) begin
        if (reset) begin
            q <= 0;
        end else if (greater_than) begin
            q <= count;
        end else if (equal) begin
            q <= sum;
        end else begin
            q <= a;
        end
    end
    
endmodule
module comparator_module (
    input [7:0] a,
    input [7:0] b,
    output reg greater_than
);
    
    always @(*) begin
        if (a > b) begin
            greater_than = 1;
        end else begin
            greater_than = 0;
        end
    end
    
endmodule
module counter_module (
    input clk,
    input reset,
    input enable,
    output reg [3:0] count
);
    
    always @(posedge clk) begin
        if (reset) begin
            count <= 0;
        end else if (enable) begin
            count <= count + 1;
        end
    end
    
endmodule
module control_logic_module (
    input [7:0] a,
    input [7:0] b,
    input greater_than,
    output reg equal,
    output reg enable
);
    
    always @(*) begin
        if (a > b) begin
            equal = 0;
            enable = 1;
        end else if (a < b) begin
            equal = 0;
            enable = 0;
        end else begin
            equal = 1;
            enable = 1;
        end
    end
    
endmodule
module functional_module (
    input a,
    input [3:0] b,
    output reg [7:0] sum
);
    
    always @(*) begin
        sum = {7'b0, a} + b;
    end
    
endmodule