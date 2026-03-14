module add_sub (
    input [31:0] a,
    input [31:0] b,
    input sub,
    output [31:0] result
);

    wire [31:0] sum;
    wire [31:0] diff;
    wire [31:0] select;
    
    assign select = sub ? ~b : b;
    
    assign sum = a + select;
    assign diff = sub ? ~select : select;
    
    assign result = sub ? diff : sum;

endmodule

module transition_detector (
    input clk,
    input reset,
    input [31:0] in,
    output reg out
);

    reg [31:0] prev;
    
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            prev <= 0;
            out <= 0;
        end
        else begin
            if (in[0] && !prev[0]) begin
                out <= 1;
            end
            else if (!in[0] && prev[0]) begin
                out <= 0;
            end
            prev <= in;
        end
    end

endmodule

module top_module (
    input clk,
    input reset,
    input [31:0] a,
    input [31:0] b,
    input sub,
    input [31:0] in,
    output [31:0] out
);

    wire [31:0] add_sub_result;
    wire transition_detector_result;
    
    add_sub add_sub_inst (
        .a(a),
        .b(b),
        .sub(sub),
        .result(add_sub_result)
    );
    
    transition_detector transition_detector_inst (
        .clk(clk),
        .reset(reset),
        .in(in),
        .out(transition_detector_result)
    );
    
    assign out = transition_detector_result ? add_sub_result - in : add_sub_result + in;

endmodule