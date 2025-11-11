
module top_module (
    input clk,
    input d1,
    input d2,
    input reset,
    input [15:0] in1,
    input [15:0] in2,
    output reg q1,
    output reg q2,
    output [15:0] out_xor,
    output [15:0] out_and,
    output [15:0] out_final
 );

    // Define the T flip-flop for D1
    reg t1;
    always @(posedge clk) begin
        if (reset) begin
            q1 <= 0;
        end else begin
            q1 <= t1;
        end
    end
    always @(posedge clk) begin
        if (reset) begin
            t1 <= 0;
        end else begin
            t1 <= d1;
        end
    end
    
    // Define the JK flip-flop for D2
    reg j2, k2;
    always @(posedge clk) begin
        if (reset) begin
            q2 <= 0;
        end else begin
            j2 <= d2;
            k2 <= ~d2;
            if (j2 && k2) begin
                q2 <= ~q2;
            end else if (j2) begin
                q2 <= 1;
            end else if (k2) begin
                q2 <= 0;
            end
        end
    end
    
    // Define the combinational circuit for XOR and AND
    assign out_xor = in1 ^ in2;
    assign out_and = in1 & in2;
    
    // Define the functional module for bitwise OR
    assign out_final = q2 | out_and;

endmodule