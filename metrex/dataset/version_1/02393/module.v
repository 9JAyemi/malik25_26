
module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [7:0] in,
    output reg [7:0] anyedge,
    output [7:0] final_out
); // RTL will be here

    reg [7:0] last_in;
    wire [7:0] xor_out;
    
    xor_detector u1 (
        .in(in),
        .last_in(last_in),
        .anyedge(xor_out)
    );
    
    always @(posedge clk or posedge reset) begin // RTL will be here
        if (reset) begin
            last_in <= 8'b0;
            anyedge <= 8'b0;
        end else begin
            last_in <= in;
            anyedge <= xor_out;
        end
    end
    
    assign final_out = xor_out | anyedge;
    
endmodule
module xor_detector (
    input [7:0] in,
    input [7:0] last_in,
    output [7:0] anyedge
);
    
    assign anyedge = in ^ last_in;

endmodule