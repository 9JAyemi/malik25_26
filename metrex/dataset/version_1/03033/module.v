
module top_module (
    input clk,
    input up_down,
    input [3:0] load,
    input SUB,
    output reg [3:0] Q
);

    wire [3:0] counter_out;
    wire [3:0] add_sub_out;
    
    up_down_counter udc (
        .clk(clk),
        .up_down(up_down),
        .load(load),
        .Q(counter_out)
    );
    
    adder_subtractor add_sub (
        .A(counter_out),
        .B(load),
        .SUB(SUB),
        .Q(add_sub_out)
    );
    
    always @(posedge clk) begin
        if (load) begin
            Q <= load;
        end else begin
            if (SUB) begin
                Q <= add_sub_out;
            end else begin
                Q <= counter_out;
            end
        end
    end
    
endmodule
module up_down_counter (
    input clk,
    input up_down,
    input [3:0] load,
    output reg [3:0] Q
);

    always @(posedge clk) begin
        if (load) begin
            Q <= load;
        end else begin
            if (up_down) begin
                Q <= Q + 1;
            end else begin
                Q <= Q - 1;
            end
        end
    end
    
endmodule
module adder_subtractor (
    input [3:0] A,
    input [3:0] B,
    input SUB,
    output reg [3:0] Q
);

    always @(A, B, SUB) begin
        if (SUB) begin
            Q <= A - B;
        end else begin
            Q <= A + B;
        end
    end
    
endmodule